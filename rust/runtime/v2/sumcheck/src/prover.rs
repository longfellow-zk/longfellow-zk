// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Numerical sumcheck over one circuit described by sparse quad fragments.
//!
//! All supplied circuits share the same input array. Intermediate wire arrays
//! concatenate the active circuits' wires, with no padding between them.
//! Evaluation saves one complete witness array per layer, from inputs to outputs;
//! proving consumes those arrays in reverse. Shorter circuits join later with
//! freshly weighted zero outputs, leaving the running claim unchanged.
//!
//! The sparse Q, L and K tensors are traversed fragment by fragment, applying
//! local-to-global offsets through slices. At the input layer every fragment has
//! offset zero. Once the tensors are bound, ordinary sumcheck operates on one W
//! array and one q_l array, indexed only by the global wire index.
//!
//! For global output weights a[g] and global input witness W, form
//!
//! ```text
//! q_l[l] = sum_g a[g] * (sum_r Q[g,l,r]*W[r] + L[g,l]),
//! K_a    = sum_g a[g]*K[g],
//! C - K_a = sum_l q_l[l]*W[l].
//! ```
//!
//! Assertion terms replace their entire weighted coefficient with an independent
//! challenge, reused in both tensor bindings. Linear terms enter q_l directly;
//! constants have no witness factor and are subtracted before the rounds.
//!
//! Folding global wire bits at u leaves exactly two terminal factors:
//!
//! ```text
//! m(u)[l] = product_j u[j]^l_j,
//! A = sum_l m(u)[l]*W[l],
//! B = sum_l m(u)[l]*q_l[l] = sum_r q_r[r]*W[r] + L(u),
//! q_r[r] = sum_{g,l} a[g]*Q[g,l,r]*m(u)[l],
//! L(u)   = sum_{g,l} a[g]*L[g,l]*m(u)[l].
//! ```
//!
//! The randomized affine terminal identity checks C=A*B. After both masked
//! factors are bound, one alpha combines them. The next weights are
//! a_next[r]=m(u)[r]+alpha*q_r[r], and the next claim is A+alpha*(B-L(u)).
//! Subtracting alpha*L(u) removes the term with no right-hand witness factor.
//! Both K_a and L(u) are recorded for the shared symbolic builder's affine rows.
//! The final dense input weights directly address the common authenticated inputs.
use super::{
    circuit::CircuitSource,
    dense::{as_scalar, bind},
    fragments::{self, Schedule, SplitFragment},
    proof::{LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry},
    split::{split_layers, SplitLayer},
    symbolic::{build_constraints, Constraints, LayerChallenges},
    transcript::{end_layer, round_challenge},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        random::RandomEngine,
        v2::transcript::{Reading, TranscriptRef},
    },
};

#[cfg(test)]
pub(crate) fn evaluate_and_prove<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    inputs: Vec<F::E>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::v2::Circuit<F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<(SumcheckProof<W, F>, Constraints<F::E>), String> {
    evaluate_and_prove_circuits(&[circuit], inputs, pads, t, f)
}

/// The caller binds all circuit statements and shared public inputs first.
/// Split each circuit once for both evaluation and proving; consume its split
/// layers and witnesses as the shared schedule advances toward the inputs.
pub(crate) fn evaluate_and_prove_circuits<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuits: &[impl CircuitSource<F>],
    inputs: Vec<F::E>,
    pads: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<(SumcheckProof<W, F>, Constraints<F::E>), String> {
    let schedule = Schedule::new(circuits)?;
    pads.validate(&schedule.geometry)
        .map_err(|e| e.to_string())?;
    if inputs.len() != schedule.ninput {
        return Err("shared input width mismatch".into());
    }
    let layers: Vec<_> = circuits.iter().map(|c| split_layers(c, f)).collect();
    let witnesses = super::eval::eval_circuits(inputs, circuits, &layers, &schedule, f)
        .map_err(|e| format!("eval_circuit failed: {e}"))?;
    prove_split(circuits, layers, witnesses, pads, schedule, t, f)
}

fn prove_split<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuits: &[impl CircuitSource<F>],
    layers: Vec<Vec<SplitLayer<'_>>>,
    witnesses: Vec<Vec<F::E>>,
    pads: &SumcheckProof<W, F>,
    schedule: Schedule,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<(SumcheckProof<W, F>, Constraints<F::E>), String> {
    pads.validate(&schedule.geometry)
        .map_err(|e| e.to_string())?;
    assert_eq!(layers.len(), circuits.len());
    assert_eq!(witnesses.len(), schedule.layers.len());
    let mut layers: Vec<_> = layers.into_iter().map(Vec::into_iter).collect();
    schedule.absorb(circuits, t);
    let mut input_assertions = Vec::new();
    let mut weights = Vec::new();
    let mut claim = f.zero();
    let mut proof_layers = Vec::with_capacity(pads.layers.len());
    let mut challenges = Vec::with_capacity(pads.layers.len());
    for ((stage, w), pp) in witnesses.into_iter().enumerate().zip(&pads.layers) {
        let layout = &schedule.layers[stage];
        assert_eq!(w.len(), layout.nw);
        let mut active: Vec<_> = layout
            .fragments
            .iter()
            .map(|s| SplitFragment::new(s, layers[s.circuit].next().expect("scheduled fragment")))
            .collect();
        schedule.start_layer(&mut weights, &mut active, stage, t, f);
        // Every fragment accumulates into its slice of one q_l. At the shared
        // input boundary those slices overlap intentionally, combining the gates.
        let mut q = vec![f.zero(); layout.nw];
        for a in &active {
            let s = &a.fragment;
            super::quad::bind_r_into(
                &a.layer,
                &circuits[s.circuit].raw().constants,
                &weights[s.output_range.clone()],
                &a.assertions,
                &w[s.input_range.clone()],
                &mut q[s.input_range.clone()],
                f,
            );
        }
        let constant = fragments::constant(circuits, &weights, &active, f);
        let (proof, mut c, mut next) =
            prove_dot_product(w, q, pp, f.subf(&claim, &constant), t, f, |r| {
                if stage + 1 == schedule.layers.len() {
                    input_assertions = schedule.input_assertions(circuits, r, f);
                }
            });
        let (next_weights, linear) = fragments::transition(
            circuits, &weights, &active, layout.nw, &c.point_l, &c.alpha, f,
        );
        weights = next_weights;
        f.fnms(&mut next, &c.alpha, &linear);
        claim = next;
        c.constant = constant;
        c.linear = linear;
        proof_layers.push(proof);
        challenges.push(c);
    }
    schedule.finish_inputs(circuits, &mut weights, input_assertions, t, f);
    let proof = SumcheckProof {
        layers: proof_layers,
    };
    let constraints = build_constraints(&proof, challenges, weights, f);
    Ok((proof, constraints))
}

/// Reduce `claim = sum_l q_l[l] W[l]`.
/// Each round binds one bit of `l` in both arrays; `point_l` is the final `u`.
/// The final scalars A = W(u), B = q_l(u) must multiply to the last round claim.
/// Return this layer's masked messages, sampled challenges, and the unmasked
/// combined claim A + alpha*B for the next layer. The caller may extend the
/// same combine answer with input assertion coefficients, using only a reader.
pub(super) fn prove_dot_product<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    mut w: Vec<F::E>,
    mut q_l: Vec<F::E>,
    pads: &LayerProof<W, F>,
    initial_claim: F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
    after_alpha: impl FnOnce(&mut Reading<'_>),
) -> (LayerProof<W, F>, LayerChallenges<F::E>, F::E) {
    let mut claim = initial_claim;
    let mut rounds = Vec::with_capacity(pads.rounds.len());
    let mut point_l = Vec::with_capacity(pads.rounds.len());
    for round_pads in &pads.rounds {
        let (m, z, claim_next) = round(&mut w, &mut q_l, round_pads, claim, transcript, f);
        claim = claim_next;
        rounds.push(m);
        point_l.push(z);
    }
    // Both arrays now contain one scalar: claims[0] = A and claims[1] = B.
    let claims = [as_scalar::<W, F>(&w), as_scalar::<W, F>(&q_l)];
    assert!(
        claim == f.mulf(&claims[0], &claims[1]),
        "single-hand terminal product mismatch"
    );
    // Hide the cross coefficient independently, before choosing the scale.
    let mut cross = f.mulf(&claims[0], &pads.claims[1]);
    f.fma(&mut cross, &claims[1], &pads.claims[0]);
    f.sub(&mut cross, &pads.cross);
    let terminal = super::transcript::terminal_challenge(&cross, transcript, f);
    let mut masked = claims.clone();
    blas::axpy(&mut masked, &terminal, &pads.claims, f);
    // Bind both masked claims before drawing their combination challenge.
    let alpha = end_layer(&masked, transcript, f, after_alpha);
    claim = claims[0].clone();
    f.fma(&mut claim, &alpha, &claims[1]);
    (
        LayerProof {
            rounds,
            cross,
            claims: masked,
        },
        LayerChallenges {
            point_l,
            alpha,
            terminal,
            constant: f.zero(),
            linear: f.zero(),
        },
        claim,
    )
}

/// Send one round's masked coefficients and bind its challenge into both arrays.
/// On entry, claim = sum_i q_l[i]*w[i]. Binding the low variable at x gives
/// p(x) = c0 + c1*x + c2*x^2, with c0 + c2 = claim. Send c0-s0,c1-s1 before
/// sampling z, then set
///
/// ```text
/// claim' = p(z) = z^2*claim + (1-z^2)*c0 + z*c1.
/// ```
///
/// After binding, claim' = sum_i q_l'[i]*w'[i], with one fewer index bit.
/// Return the masked message, z, and the next claim.
fn round<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    w: &mut Vec<F::E>,
    q_l: &mut Vec<F::E>,
    pads: &RoundPoly<W, F>,
    claim: F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> (RoundPoly<W, F>, F::E, F::E) {
    let p = quad_round_poly(q_l, w, &claim, f);
    let (m, z, claim_next) = mask_round(p, pads, claim, transcript, f);
    bind(w, &z, f);
    bind(q_l, &z, f);
    (m, z, claim_next)
}
/// Shared masking, challenge sampling and claim update for every numerical kernel.
pub(super) fn mask_round<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    p: RoundPoly<W, F>,
    pads: &RoundPoly<W, F>,
    claim: F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> (RoundPoly<W, F>, F::E, F::E) {
    let mut m = p.clone();
    // The transcript receives m[j] = c_j - s_j for j = 0,1; p retains the
    // unmasked coefficients used to compute the next claim.
    blas::sub(&mut m.coefficients, &pads.coefficients, f);
    let z = round_challenge(&m, transcript, f);

    // The constant and quadratic coefficients partition the incoming sum:
    // c0 = sum_i q_l[2i]*w[2i], c2 = sum_i q_l[2i+1]*w[2i+1].
    // Thus claim = c0 + c2 supplies the missing coefficient c2 = claim - c0.
    // Evaluating p(x) = c0 + c1*x + c2*x^2 at z gives
    // claim' = c0 + z*c1 + z^2*(claim - c0)
    //        = z^2*claim + (1-z^2)*c0 + z*c1.
    let z2 = f.mulf(&z, &z);
    let one_minus_z2 = f.subf(&f.one(), &z2);
    let [c0, c1] = &p.coefficients;
    let mut claim_next = claim;
    f.mul(&mut claim_next, &z2);
    f.fma(&mut claim_next, &one_minus_z2, c0);
    f.fma(&mut claim_next, &z, c1);

    (m, z, claim_next)
}

/// Compute the constant and linear coefficients of the round polynomial.
///
/// ```text
/// p(x) = sum_i (q_l[2i] + x*q_l[2i+1]) (w[2i] + x*w[2i+1])
///      = c0 + c1*x + c2*x^2,
/// claim = c0 + c2.
/// ```
///
/// Accumulate c0 and p(1) together, then obtain c1 = p(1) - claim.
/// This uses two products per pair; missing odd coefficients are zero.
#[inline]
pub(super) fn quad_round_poly<const W: usize, F: RuntimeField<W> + SerializableField>(
    q_l: &[F::E],
    w: &[F::E],
    claim: &F::E,
    f: &F,
) -> RoundPoly<W, F> {
    assert_eq!(q_l.len(), w.len());
    let n = q_l.len();
    let pairs = n / 2;
    let mut accum_c0 = f.zero_accum();
    let mut accum_p1 = f.zero_accum();

    for i in 0..pairs {
        let idx = 2 * i;
        f.mac(&mut accum_c0, &q_l[idx], &w[idx]);
        let q_sum = f.addf(&q_l[idx], &q_l[idx + 1]);
        let w_sum = f.addf(&w[idx], &w[idx + 1]);
        f.mac(&mut accum_p1, &q_sum, &w_sum);
    }

    if !n.is_multiple_of(2) {
        // With zero odd coefficients, the unpaired product is constant in x
        // and contributes equally to c0 and p(1).
        let last = n - 1;
        f.mac(&mut accum_c0, &q_l[last], &w[last]);
        f.mac(&mut accum_p1, &q_l[last], &w[last]);
    }

    let c0 = f.accum_reduce(&accum_c0);
    let p1 = f.accum_reduce(&accum_p1);
    // p(1) = c0 + c1 + c2; subtract claim = c0 + c2 to isolate c1.
    let c1 = f.subf(&p1, claim);
    RoundPoly {
        coefficients: [c0, c1],
    }
}

/// Sample additive sumcheck pads and their flattened commitment witness.
/// The structured copy matches the proof's round and claim slots for masking.
/// The flat copy follows the codec's committed-pad layout: two pads per round,
/// then p_A,p_B,p_AB,p_D for each layer. The honest prover sets p_AB=p_A*p_B,
/// but Polygero enforces only affine equations on these cells. The cross message
/// and fresh terminal scale check a random-point identity instead.
pub(crate) fn sample_pads<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    R: RandomEngine,
>(
    geometry: &SumcheckProofGeometry,
    rng: &mut R,
    f: &F,
) -> (SumcheckProof<W, F>, Vec<F::E>) {
    let npads = geometry.pad_count().expect("valid pad geometry");
    let mut witness = Vec::with_capacity(npads);
    let mut proof_layers = Vec::with_capacity(geometry.logw_layers.len());
    for &logw in &geometry.logw_layers {
        let mut rounds = Vec::with_capacity(logw);
        for _ in 0..logw {
            let round_pads = [rng.elt_field(f), rng.elt_field(f)];
            witness.extend(round_pads.clone());
            rounds.push(RoundPoly {
                coefficients: round_pads,
            });
        }
        let claim_pads = [rng.elt_field(f), rng.elt_field(f)];
        witness.extend(claim_pads.clone());
        witness.push(f.mulf(&claim_pads[0], &claim_pads[1]));
        let cross = rng.elt_field(f);
        witness.push(cross.clone());
        proof_layers.push(LayerProof {
            rounds,
            cross,
            claims: claim_pads,
        });
    }
    (
        SumcheckProof {
            layers: proof_layers,
        },
        witness,
    )
}

#[cfg(test)]
#[path = "../tests/prover_fixtures.rs"]
mod fixtures;
#[cfg(test)]
pub(crate) use fixtures::{prove, prove_core};
