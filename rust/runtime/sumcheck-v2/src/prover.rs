// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Prove each circuit layer from outputs toward inputs, carrying one weighted claim.
//!
//! The ZK caller supplies each layer's input witness W and secret pads already
//! covered by its commitment. Layers run from circuit outputs toward inputs.
//! Initially, a contains sampled weights on the circuit outputs and claim is
//! zero, since every output must vanish. For each layer, first form
//!
//! ```text
//! q_l[l] = sum_{g,r} a[g] QUAD[g,l,r] W[r],
//! claim = sum_l q_l[l] W[l].
//! ```
//!
//! `layer` forms this dot-product claim and calls `prove_dot_product`. Each
//! `round` sends two masked polynomial coefficients, samples z, and binds one
//! wire-index coordinate in both arrays. After all coordinates
//! are bound at u, the arrays contain two scalars A and B:
//!
//! ```text
//! m_l[l] = product_j u[j]^l_j,
//! A = sum_l m_l[l] W[l],
//! B = sum_l m_l[l] q_l[l] = sum_r q_r[r] W[r],
//! q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] m_l[l],
//! ```
//!
//! Their product must equal the final round claim. Send the masked A,B before
//! sampling alpha. `weights_next` makes their combined claim the starting point
//! for the next layer, where these input wires become output wires:
//!
//! ```text
//! a_next[r] = m_l[r] + alpha*q_r[r],
//! claim_next = A + alpha*B = sum_r a_next[r] W[r].
//! ```
//!
//! Assertion quads use sampled coefficients in place of a[g] QUAD[g,l,r].
//! The prover records the challenges as it runs, then uses the shared symbolic
//! builder to express the same round updates and product checks as constraints
//! on the committed pads. The last claim is constrained to the weighted circuit
//! inputs. Return these constraints alongside the masked proof messages.

#[cfg(test)]
use crate::runtime::sumcheck_v2::TranscriptSumcheck;
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{blas, ElementOf, RuntimeField, SupportsSampling},
        proto::sumcheck_v2::pad_count,
        random::{RandomEngine, Transcript},
        sumcheck_v2::{
            dense::{as_scalar, bind},
            proof::{LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry},
            quad::{bind_r, weights_next},
            symbolic::{build_constraints, Constraints, LayerChallenges},
            transcript::{assertion_weights, begin, end_layer, round_challenge},
        },
    },
};

/// Prove after the caller has bound the statement to the transcript.
/// `w_layers[j]` contains layer j's input witness, in circuit output-to-input order.
/// At each iteration, a weights that layer's outputs and claim is their weighted
/// sum. `layer` proves its dot product and returns weights and a claim on its
/// input wires. Return the masked proof messages and the symbolic constraints
/// reconstructed from the sampled challenges.
pub(crate) fn prove_core<const W: usize, F: SerializableField + SupportsSampling<W>>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    prove_core_with_kernel(w_layers, pads, circuit, transcript, f, &GenericKernel)
}

/// Numerical kernels vary independently of the masked transcript protocol.
pub(super) trait ProverKernel<const W: usize, F: SerializableField + SupportsSampling<W>> {
    #[allow(clippy::too_many_arguments)]
    fn bind_r(
        &self,
        index: usize,
        layer: &crate::core::proto::Layer<F>,
        constants: &[F::E],
        a: &[F::E],
        assertions: &[F::E],
        w: &[F::E],
        f: &F,
    ) -> Vec<F::E>;
    #[allow(clippy::too_many_arguments)]
    fn dot_product(
        &self,
        index: usize,
        w: Vec<F::E>,
        q: Vec<F::E>,
        pads: &LayerProof<W, F>,
        claim: F::E,
        t: &mut Transcript,
        f: &F,
    ) -> (LayerProof<W, F>, LayerChallenges<F::E>, F::E);
}
struct GenericKernel;
impl<const W: usize, F: SerializableField + SupportsSampling<W>> ProverKernel<W, F>
    for GenericKernel
{
    fn bind_r(
        &self,
        _: usize,
        layer: &crate::core::proto::Layer<F>,
        constants: &[F::E],
        a: &[F::E],
        assertions: &[F::E],
        w: &[F::E],
        f: &F,
    ) -> Vec<F::E> {
        bind_r(layer, constants, a, assertions, w, f)
    }
    fn dot_product(
        &self,
        _: usize,
        w: Vec<F::E>,
        q: Vec<F::E>,
        pads: &LayerProof<W, F>,
        claim: F::E,
        t: &mut Transcript,
        f: &F,
    ) -> (LayerProof<W, F>, LayerChallenges<F::E>, F::E) {
        prove_dot_product(w, q, pads, claim, t, f)
    }
}
pub(super) fn prove_core_with_kernel<
    const W: usize,
    F: SerializableField + SupportsSampling<W>,
    K: ProverKernel<W, F>,
    I,
>(
    witnesses: I,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
    kernel: &K,
) -> (SumcheckProof<W, F>, Constraints<F::E>)
where
    I: IntoIterator<Item = Vec<F::E>>,
    I::IntoIter: ExactSizeIterator,
{
    let w_layers = witnesses.into_iter();
    pads.validate(&SumcheckProofGeometry::from_circuit(circuit))
        .expect("pad shape mismatch");
    assert_eq!(w_layers.len(), circuit.raw.layers.len());
    let mut a = begin(circuit, transcript, f);
    let mut claim = f.zero();
    let mut proof_layers = Vec::with_capacity(w_layers.len());
    let mut layer_challenges = Vec::with_capacity(w_layers.len());
    for (layer_index, w) in w_layers.into_iter().enumerate() {
        let (proof, challenges, a_next, claim_next) = layer(
            kernel,
            layer_index,
            w,
            &pads.layers[layer_index],
            circuit,
            &a,
            claim,
            transcript,
            f,
        );
        a = a_next;
        claim = claim_next;
        proof_layers.push(proof);
        layer_challenges.push(challenges);
    }
    let proof = SumcheckProof {
        layers: proof_layers,
    };
    let constraints = build_constraints(&proof, layer_challenges, a, f);
    (proof, constraints)
}

/// Prove one circuit layer and carry its weighted claim to the layer's inputs.
/// Bind QUAD with the incoming output weights a and witness W to obtain
/// q_l[l] = sum_{g,r} a[g]*QUAD[g,l,r]*W[r]. Prove claim = sum_l q_l[l]*W[l].
/// Return the proof messages, sampled challenges, and the next weighted claim:
/// a_next and claim_next = sum_r a_next[r]*W[r].
/// Assertion coefficients are sampled once and reused in both tensor bindings.
#[allow(clippy::too_many_arguments)]
fn layer<const W: usize, F: SerializableField + SupportsSampling<W>, K: ProverKernel<W, F>>(
    kernel: &K,
    layer_index: usize,
    w: Vec<F::E>,
    pads: &LayerProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    a: &[F::E],
    claim: F::E,
    transcript: &mut Transcript,
    f: &F,
) -> (LayerProof<W, F>, LayerChallenges<F::E>, Vec<F::E>, F::E) {
    let circuit_layer = &circuit.raw.layers[layer_index];
    let constants = &circuit.raw.constants;
    assert!(circuit_layer.nw() > 0, "sumcheck layer must contain a wire");
    assert_eq!(w.len(), circuit_layer.nw(), "layer witness width mismatch");

    let assertions = assertion_weights(circuit_layer, constants, layer_index, transcript, f);
    let q_l = kernel.bind_r(layer_index, circuit_layer, constants, a, &assertions, &w, f);
    let (proof, challenges, claim_next) =
        kernel.dot_product(layer_index, w, q_l, pads, claim, transcript, f);

    // A + alpha*B = sum_r (m_l[r] + alpha*q_r[r])*W[r].
    let a_next = weights_next(
        circuit_layer,
        constants,
        a,
        &assertions,
        &challenges.point_l,
        &challenges.alpha,
        f,
    );
    (proof, challenges, a_next, claim_next)
}

/// Reduce `claim = sum_l q_l[l] W[l]`.
/// Each round binds one bit of `l` in both arrays; `point_l` is the final `u`.
/// The final scalars A = W(u), B = q_l(u) must multiply to the last round claim.
/// Return this layer's masked messages, sampled challenges, and the unmasked
/// combined claim A + alpha*B for the next layer.
pub(super) fn prove_dot_product<const W: usize, F: SerializableField + SupportsSampling<W>>(
    mut w: Vec<F::E>,
    mut q_l: Vec<F::E>,
    pads: &LayerProof<W, F>,
    initial_claim: F::E,
    transcript: &mut Transcript,
    f: &F,
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
    finish_dot_product(&w, &q_l, pads, claim, rounds, point_l, transcript, f)
}
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_dot_product<const W: usize, F: SerializableField + SupportsSampling<W>>(
    w: &[F::E],
    q_l: &[F::E],
    pads: &LayerProof<W, F>,
    mut claim: F::E,
    rounds: Vec<RoundPoly<W, F>>,
    point_l: Vec<F::E>,
    transcript: &mut Transcript,
    f: &F,
) -> (LayerProof<W, F>, LayerChallenges<F::E>, F::E) {
    // Both arrays now contain one scalar: claims[0] = A and claims[1] = B.
    let claims = [as_scalar::<W, F>(w), as_scalar::<W, F>(q_l)];
    assert_eq!(
        claim,
        f.mulf(&claims[0], &claims[1]),
        "single-hand terminal product mismatch"
    );
    let mut masked = claims.clone();
    // Send m_A = A - p_A and m_B = B - p_B. Symbolic verification restores
    // the hidden claims as message + pad before forming claim - A*B = 0.
    blas::sub(&mut masked, &pads.claims, f);
    // Bind both masked claims before drawing their combination challenge.
    let alpha = end_layer(&masked, transcript, f);
    claim = claims[0].clone();
    f.fma(&mut claim, &alpha, &claims[1]);
    (
        LayerProof {
            rounds,
            claims: masked,
        },
        LayerChallenges { point_l, alpha },
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
fn round<const W: usize, F: SerializableField + SupportsSampling<W>>(
    w: &mut Vec<F::E>,
    q_l: &mut Vec<F::E>,
    pads: &RoundPoly<W, F>,
    claim: F::E,
    transcript: &mut Transcript,
    f: &F,
) -> (RoundPoly<W, F>, F::E, F::E) {
    let p = quad_round_poly(q_l, w, &claim, f);
    let (m, z, claim_next) = mask_round(p, pads, claim, transcript, f);
    bind(w, &z, f);
    bind(q_l, &z, f);
    (m, z, claim_next)
}
/// Shared masking, challenge sampling and claim update for every numerical kernel.
pub(super) fn mask_round<const W: usize, F: SerializableField + SupportsSampling<W>>(
    p: RoundPoly<W, F>,
    pads: &RoundPoly<W, F>,
    claim: F::E,
    transcript: &mut Transcript,
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
    q_l: &[ElementOf<F>],
    w: &[ElementOf<F>],
    claim: &ElementOf<F>,
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
/// then p_A,p_B,p_A*p_B for each layer. The product slot lets the ZK compiler
/// express claim - A*B as a linear constraint on committed values; Polygero also
/// enforces that the product slot equals p_A*p_B.
pub(crate) fn sample_pads<
    const W: usize,
    F: SerializableField + SupportsSampling<W>,
    R: RandomEngine,
>(
    geometry: &SumcheckProofGeometry,
    rng: &mut R,
    f: &F,
) -> (SumcheckProof<W, F>, Vec<ElementOf<F>>) {
    let npads = geometry
        .logw_layers
        .iter()
        .map(|&logw| pad_count(logw))
        .sum();
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
        proof_layers.push(LayerProof {
            rounds,
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

/// Bind the statement and run the prover for a test with at least one layer.
/// The final entry of w_layers supplies the circuit inputs; zero-layer tests
/// bind the statement explicitly and call prove_core.
#[cfg(test)]
pub(crate) fn prove<const W: usize, F: SerializableField + SupportsSampling<W>>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    let inputs = w_layers
        .last()
        .expect("use prove_core for a zero-layer circuit");
    transcript.write_sumcheck_statement(circuit, &inputs[..circuit.raw.npublic_input], f);
    prove_core(w_layers, pads, circuit, transcript, f)
}
