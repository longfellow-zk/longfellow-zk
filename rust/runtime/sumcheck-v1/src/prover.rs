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

//! Prove v1 circuit layers from outputs to inputs, carrying two witness claims.
//!
//! At each layer, alpha combines the preceding claims and their output weights.
//! Binding g in QUAD[g,l,r] leaves Q[r,l]. Each round first binds one bit of r
//! (hand 0), then one bit of l (hand 1), proving the sum of Q[r,l]*W[r]*W[l].
//! The round polynomial satisfies p(0)+p(1)=claim; only p(0) and p(pt(2)) are
//! sent, after subtracting their committed pads. Interpolation at the challenge
//! gives the next claim. The fully bound product yields two witness claims for
//! the next circuit layer. Their combination happens at that layer's beginning.
//!
//! `prove_core` records interpolation coefficients alongside the proof, allowing
//! the shared symbolic builder to construct the same constraints as the verifier.
//! Witness bindings reuse owned buffers; the initial two hands share one buffer
//! until the first binding separates them.
use crate::{
    core::algebra::ElementOf,
    runtime::{
        algebra::{poly::InterpolationField, SupportsSampling},
        random::{RandomEngine, Transcript},
        sumcheck_v1::{
            hquad::HQuad,
            poly::{Poly, QuadRoundPoly, QuadWirePoly},
            proof::{LayerProof, SumcheckProof, MAX_LOGW},
            transcript::TranscriptSumcheck,
            verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData},
            LagrangeBasis,
        },
    },
};

/// The two points and logical width describing the current pair of output claims.
struct Bindings<const W: usize, F: InterpolationField<W>> {
    logv: usize,
    nv: usize,
    challenges: [Vec<ElementOf<F>>; 2],
}

/// Bind the circuit statement and public input prefix, then prove every layer.
pub fn prove<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, VerifierData<ElementOf<F>>) {
    assert!(
        circuit.raw.ninput >= circuit.raw.npublic_input,
        "npublic_input ({}) exceeds ninput ({})",
        circuit.raw.npublic_input,
        circuit.raw.ninput
    );

    let inputs = &in_layers[circuit.raw.layers.len() - 1];
    assert!(
        inputs.len() >= circuit.raw.npublic_input,
        "input vector too short: expected at least npublic_input ({}) entries, got {}",
        circuit.raw.npublic_input,
        inputs.len()
    );
    let public_inputs = &inputs[..circuit.raw.npublic_input];
    transcript.write_sumcheck_statement(circuit, public_inputs, f);
    prove_core(in_layers, pad, circuit, transcript, f)
}

/// Prove after the caller has bound the statement to the transcript. Layer inputs
/// arrive in circuit output-to-input order; return messages and local verifier data.
pub fn prove_core<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    mut in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, VerifierData<ElementOf<F>>) {
    pad.validate(&crate::runtime::sumcheck_v1::proof::SumcheckProofGeometry::from_circuit(circuit))
        .expect("pad shape mismatch");
    // The wire array is conceptually infinite (padded with zeros), but we normalize
    // each layer's wire vector to contain at least one 0 to simplify the implementation
    // and avoid handling the empty vec case in downstream binding functions.
    for wires in &mut in_layers {
        *wires = crate::runtime::sumcheck_v1::dense::normalize(std::mem::take(wires), f);
    }
    let mut bindings = {
        // Consume both legacy challenge vectors even though only gate points
        // are needed. Their sampling order is part of the transcript format.
        let (_copy_challenges, challenges_0) = transcript.begin_circuit(f);
        Bindings {
            logv: circuit.raw.logv,
            nv: circuit.raw.noutput,
            challenges: [
                challenges_0[..circuit.raw.logv].to_vec(),
                challenges_0[..circuit.raw.logv].to_vec(),
            ],
        }
    };

    let num_layers = circuit.raw.layers.len();
    assert!(in_layers.len() >= num_layers && pad.layers.len() >= num_layers);
    let layers_slice = &circuit.raw.layers[..num_layers];
    let in_layers_slice = &mut in_layers[..num_layers];
    let pad_layers_slice = &pad.layers[..num_layers];

    let mut claims = [f.zero(), f.zero()];
    let mut layers = Vec::with_capacity(num_layers);
    let mut verifier_layers = Vec::with_capacity(num_layers);

    for i in 0..num_layers {
        let clr = &layers_slice[i];
        let (alpha, beta) = transcript.begin_layer(f);
        let wires = std::mem::take(&mut in_layers_slice[i]);
        let hquad = HQuad::bind_g(
            clr,
            &circuit.raw.constants,
            bindings.logv,
            bindings.nv,
            &bindings.challenges[0],
            &bindings.challenges[1],
            &alpha,
            &beta,
            f,
        );
        let (layer_proof, bindings_next, claims_next, layer_data) = layer(
            clr.logw(),
            clr.nw(),
            wires,
            &pad_layers_slice[i],
            transcript,
            hquad,
            &alpha,
            claims,
            f,
        );
        bindings = bindings_next;
        claims = claims_next;

        verifier_layers.push(layer_data);
        layers.push(layer_proof);
    }

    // This is the legacy ZK verifier's final input-combination challenge.
    let input_alpha = transcript.elt_field(f);
    let input_weights = crate::runtime::sumcheck_v1::eq::eq2(
        bindings.logv,
        circuit.raw.ninput,
        &bindings.challenges[0],
        &bindings.challenges[1],
        &input_alpha,
        f,
    );
    (
        SumcheckProof { layers },
        VerifierData {
            layers: verifier_layers,
            input_alpha,
            input_weights,
        },
    )
}

/// Prove one layer with alternating r/l bindings. Return the two unmasked witness
/// claims and their points, together with masked messages and interpolation data.
#[allow(clippy::too_many_arguments)]
fn layer<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    logw: usize,
    nw: usize,
    wires: Vec<ElementOf<F>>,
    pad: &LayerProof<W, F>,
    transcript: &mut Transcript,
    mut hquad: HQuad<W, F>,
    alpha: &ElementOf<F>,
    claims: [ElementOf<F>; 2],
    f: &F,
) -> (
    LayerProof<W, F>,
    Bindings<W, F>,
    [ElementOf<F>; 2],
    LayerVerifierData<ElementOf<F>>,
) {
    assert!(
        crate::runtime::sumcheck_v1::sane_logw(logw),
        "logw must be sane"
    );
    assert!(
        wires.len() as u64 <= (1u64 << logw),
        "size of wires {} exceeds 2^logw {}",
        wires.len(),
        1u64 << logw
    );
    let mut challenges = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut round_polys = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut round_coefficients = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let basis = LagrangeBasis::new(f);
    let mut sum = claims[0].clone();
    f.fma(&mut sum, alpha, &claims[1]);

    // Wrap the initial wire vector in an Rc to avoid cloning the massive input slice.
    // At round 0, both right hand (w[0]) and left hand (w[1]) point to the same shared buffer.
    let wires_rc = std::rc::Rc::new(wires);
    let mut w = [wires_rc.clone(), wires_rc];
    let mut qw = vec![f.zero(); w[0].len()];

    for round in 0..logw {
        for hand in 0..2 {
            let other_hand = 1 - hand;
            let wh_hand = &w[hand];
            let wh_other_hand = &w[other_hand];

            let wh_size = wh_hand.len();
            fill_round_weights(&mut qw[..wh_size], &hquad, wh_other_hand, hand, f);

            let evaluations = quad_round_poly(wh_size, &qw[..wh_size], wh_hand, &sum, f);

            assert!(round < MAX_LOGW);
            let round_values = evaluations.to_wire();
            let message = round_values.sub(&pad.hp[hand][round], f);
            let round_challenge = transcript.round(&message, f);
            let coefficients = RoundCoefficients::new(&basis, &round_challenge, f);
            sum = coefficients.evaluate(&round_values, &sum, f);
            round_coefficients[hand].push(coefficients);
            round_polys[hand].push(message);
            challenges[hand].push(round_challenge.clone());

            // The first right-hand binding allocates a half-sized buffer while
            // the left hand retains the original witness. Each hand then owns
            // its buffer exclusively, so subsequent bindings reuse it in place.
            if let Some(v) = std::rc::Rc::get_mut(&mut w[hand]) {
                crate::runtime::sumcheck_v1::dense::bind(v, &round_challenge, f);
            } else {
                let bound_v = crate::runtime::sumcheck_v1::dense::bind_out_of_place(
                    &w[hand],
                    &round_challenge,
                    f,
                );
                w[hand] = std::rc::Rc::new(bound_v);
            }
            hquad.bind_h(&round_challenge, hand, f);
        }
    }

    let claims_next = [
        crate::runtime::sumcheck_v1::dense::as_scalar::<W, F>(&w[0]),
        crate::runtime::sumcheck_v1::dense::as_scalar::<W, F>(&w[1]),
    ];

    let hquad_scalar = hquad.scalar();
    let mut expected_sum = claims_next[0].clone();
    f.mul(&mut expected_sum, &claims_next[1]);
    f.mul(&mut expected_sum, &hquad_scalar);
    assert_eq!(
        sum, expected_sum,
        "reconstructed sum does not match expected"
    );

    let mut proof_claims = [claims_next[0].clone(), claims_next[1].clone()];
    f.sub(&mut proof_claims[0], &pad.claims[0]);
    f.sub(&mut proof_claims[1], &pad.claims[1]);
    transcript.end_layer(&proof_claims, f);

    let bindings = Bindings {
        logv: logw,
        nv: nw,
        challenges,
    };

    (
        LayerProof {
            hp: round_polys,
            claims: proof_claims, // padded
        },
        bindings,
        claims_next,
        LayerVerifierData {
            rounds: round_coefficients,
            alpha: alpha.clone(),
            bound_quad: hquad_scalar,
        },
    )
}

/// For hand 0, compute qw[r] = sum_l Q[r,l]*W[l]; for hand 1, compute
/// qw[l] = sum_r Q[r,l]*W[r]. Preserve sparse-corner order in each accumulation.
/// The caller supplies the buffer reused across all rounds of this layer.
fn fill_round_weights<const W: usize, F: InterpolationField<W>>(
    qw: &mut [ElementOf<F>],
    quad: &HQuad<W, F>,
    w_other: &[ElementOf<F>],
    hand: usize,
    f: &F,
) {
    crate::runtime::algebra::blas::clear(qw, f);
    for i in 0..quad.hc.len() {
        let h = quad.hc[i].h[hand] as usize;
        let other = quad.hc[i].h[1 - hand] as usize;
        f.fma(&mut qw[h], &quad.vc[i], &w_other[other]);
    }
}

/// Evaluates the quad round polynomial of degree 2 (represented
/// by 3 evaluation points) for the current sumcheck prover round.
///
/// Directly computes the evaluations [g(0), g(1), g(2)] without intermediate
/// monomial or Newton conversions.
#[inline]
fn quad_round_poly<const W: usize, F: InterpolationField<W>>(
    n: usize,
    qw: &[ElementOf<F>],
    witness_values: &[ElementOf<F>],
    sum: &ElementOf<F>,
    f: &F,
) -> Poly<3, W, F> {
    let num_pairs = n / 2;
    let mut accum_a0 = f.zero_accum();
    let mut accum_a2 = f.zero_accum();

    for i in 0..num_pairs {
        let idx = 2 * i;
        f.mac(&mut accum_a0, &qw[idx], &witness_values[idx]);
        let dqw = f.subf(&qw[idx + 1], &qw[idx]);
        let dw = f.subf(&witness_values[idx + 1], &witness_values[idx]);
        f.mac(&mut accum_a2, &dqw, &dw);
    }

    if !n.is_multiple_of(2) {
        let last = n - 1;
        f.mac(&mut accum_a0, &qw[last], &witness_values[last]);
        f.mac(&mut accum_a2, &qw[last], &witness_values[last]);
    }

    let a0 = f.accum_reduce(&accum_a0);
    let a2 = f.accum_reduce(&accum_a2);

    // g(0) = a0
    // g(1) = sum - a0
    let mut g1 = sum.clone();
    f.sub(&mut g1, &a0);

    // c1 = g(1) - a0 - a2 = sum - 2*a0 - a2
    let mut c1 = g1.clone();
    f.sub(&mut c1, &a0);
    f.sub(&mut c1, &a2);

    // Evaluate g(2) = a2*pt(2)^2 + c1*pt(2) + a0 using Horner's method for binary field
    // compatibility:
    let pt2 = f.poly_evaluation_point(2);
    let mut g2 = a2.clone();
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &c1);
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &a0);

    Poly {
        evaluations: [a0, g1, g2],
    }
}
