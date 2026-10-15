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

use core_algebra::ElementOf;
use runtime_algebra::{poly::InterpolationField, SupportsSampling};
use runtime_random::Transcript;

use crate::{
    poly::{Poly, QuadRoundPoly, QuadWirePoly},
    proof::{LayerProof, SumcheckProof, MAX_LOGW},
    transcript::TranscriptSumcheck,
};

struct Bindings<const W: usize, F: InterpolationField<W>> {
    logv: usize,
    nv: usize,
    challenges: [Vec<ElementOf<F>>; 2],
}

pub struct SumcheckProofAux<const W: usize, F: InterpolationField<W>> {
    pub bound_quad: Vec<ElementOf<F>>,
}

impl<const W: usize, F: InterpolationField<W>> SumcheckProofAux<W, F> {
    pub fn new(num_layers: usize, f: &F) -> Self {
        Self {
            bound_quad: vec![f.zero(); num_layers],
        }
    }
}

pub fn prove<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>) {
    prove_with_order(
        in_layers,
        pad,
        circuit,
        transcript,
        f,
        crate::SumcheckOrder::default(),
    )
}

/// Prove with an explicit challenge schedule. Round-major requires stored
/// Morton traversal; hand-major accepts any stored term traversal.
pub fn prove_with_order<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
    order: crate::SumcheckOrder,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>) {
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
    prove_core_with_order(in_layers, pad, circuit, transcript, f, order)
}

pub fn prove_core<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>) {
    prove_core_with_order(
        in_layers,
        pad,
        circuit,
        transcript,
        f,
        crate::SumcheckOrder::default(),
    )
}

/// Core prover after the caller has bound the circuit statement to the transcript.
/// Round-major requires Morton-ordered circuit terms, as in [`prove_with_order`].
pub fn prove_core_with_order<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    mut in_layers: Vec<Vec<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
    order: crate::SumcheckOrder,
) -> (SumcheckProof<W, F>, SumcheckProofAux<W, F>) {
    // The wire array is conceptually infinite (padded with zeros), but we normalize
    // each layer's wire vector to contain at least one 0 to simplify the implementation
    // and avoid handling the empty vec case in downstream binding functions.
    for wires in &mut in_layers {
        *wires = crate::dense::normalize(std::mem::take(wires), f);
    }
    let (_copy_challenges, challenges_0) = transcript.begin_circuit(f);
    let mut bindings = Bindings {
        logv: circuit.raw.logv,
        nv: circuit.raw.noutput,
        challenges: [
            challenges_0[..circuit.raw.logv].to_vec(),
            challenges_0[..circuit.raw.logv].to_vec(),
        ],
    };

    let num_layers = circuit.raw.layers.len();
    assert!(in_layers.len() >= num_layers && pad.layers.len() >= num_layers);
    let layers_slice = &circuit.raw.layers[..num_layers];
    let in_layers_slice = &mut in_layers[..num_layers];
    let pad_layers_slice = &pad.layers[..num_layers];

    let mut claims = [f.zero(), f.zero()];
    let mut layers = Vec::with_capacity(num_layers);
    let mut bound_quad = Vec::with_capacity(num_layers);

    for i in 0..num_layers {
        let clr = &layers_slice[i];
        let (alpha, beta) = transcript.begin_layer(f);
        let wires = std::mem::take(&mut in_layers_slice[i]);
        let g_binding = if bindings.nv == 0 {
            Vec::new()
        } else {
            crate::eq::eq2(
                bindings.logv,
                bindings.nv,
                &bindings.challenges[0],
                &bindings.challenges[1],
                &alpha,
                f,
            )
        };
        let layer_kernel = match order {
            crate::SumcheckOrder::HandMajor => layer,
            crate::SumcheckOrder::RoundMajor => layer_round_major,
        };
        let (layer_proof, new_bindings, new_claims, quad_scalar) = layer_kernel(
            clr,
            &circuit.raw.constants,
            wires,
            &pad_layers_slice[i],
            transcript,
            &g_binding,
            &alpha,
            &beta,
            claims,
            f,
        );
        bindings = new_bindings;
        claims = new_claims;

        bound_quad.push(quad_scalar);
        layers.push(layer_proof);
    }

    (SumcheckProof { layers }, SumcheckProofAux { bound_quad })
}

#[allow(clippy::too_many_arguments)]
fn layer<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    clr: &core_proto::Layer<F>,
    constants: &[ElementOf<F>],
    mut wires: Vec<ElementOf<F>>,
    pad: &LayerProof<W, F>,
    transcript: &mut Transcript,
    g_binding: &[ElementOf<F>],
    alpha: &ElementOf<F>,
    beta: &ElementOf<F>,
    claims: [ElementOf<F>; 2],
    f: &F,
) -> (
    LayerProof<W, F>,
    Bindings<W, F>,
    [ElementOf<F>; 2],
    ElementOf<F>,
) {
    let logw = clr.logw();
    let nw = clr.nw();
    assert!(crate::sane_logw(logw), "logw must be sane");
    let dense_width = nw.max(1);
    assert!(dense_width as u64 <= (1u64 << logw));
    assert!(wires.len() <= dense_width, "witness exceeds layer width");
    wires.resize(dense_width, f.zero());
    let mut challenges = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut round_polys = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut next_claims = [f.zero(), f.zero()];
    let mut sum = claims[0].clone();
    f.fma(&mut sum, alpha, &claims[1]);
    let one = f.one();
    let mut weights = Vec::with_capacity(dense_width);

    for hand in crate::HAND_ORDER {
        weights.clear();
        weights.resize(dense_width, f.zero());
        if hand == 0 {
            // Q0(h0) = sum_{g,h1} G(g) k W(h1).
            crate::quad::accumulate_hand(
                clr,
                constants,
                g_binding,
                beta,
                &wires,
                0,
                &mut weights,
                f,
            );
        } else {
            // Q1(h1) = sum_{g,h0} G(g) k EQ(r0,h0).
            // The equality table is needed only for this one circuit scan.
            let h0_binding = crate::eq::eq1(logw, nw, &challenges[0], f);
            crate::quad::accumulate_hand(
                clr,
                constants,
                g_binding,
                beta,
                &h0_binding,
                1,
                &mut weights,
                f,
            );
        }

        // Preserve the original witness for phase 1. Only weights and working_wires
        // are folded per round; neither terms nor an HQuad are visited here.
        let mut working_wires = if hand == 0 {
            wires.clone()
        } else {
            std::mem::take(&mut wires)
        };
        // Keep Q1 unscaled so its final scalar is the unmasked wiring polynomial
        // needed by the symbolic verifier. Scale round evaluations by W(r0)
        // instead of dividing the claim by W(r0), which may be zero.
        let scale = if hand == 0 { &one } else { &next_claims[0] };
        for round in 0..logw {
            let evaluations =
                quad_round_poly(weights.len(), &weights, &working_wires, &sum, scale, f);
            assert!(round < MAX_LOGW);
            let challenge = sample_round_challenge(
                transcript,
                &evaluations,
                &pad.hp[hand][round],
                &mut round_polys[hand],
                &mut challenges[hand],
                f,
            );
            sum = evaluations.eval_lagrange(&challenge, f);
            crate::dense::bind(&mut weights, &challenge, f);
            crate::dense::bind(&mut working_wires, &challenge, f);
        }
        next_claims[hand] = crate::dense::as_scalar::<W, F>(&working_wires);
    }

    let quad_scalar = crate::dense::as_scalar::<W, F>(&weights);
    finish_layer(
        logw,
        nw,
        challenges,
        round_polys,
        next_claims,
        quad_scalar,
        sum,
        pad,
        transcript,
        f,
    )
}

/// Legacy interleaved protocol. The stored circuit must already have Morton
/// traversal; binding g preserves that order and coalesces adjacent equal pairs.
#[allow(clippy::too_many_arguments)]
fn layer_round_major<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    clr: &core_proto::Layer<F>,
    constants: &[ElementOf<F>],
    mut wires: Vec<ElementOf<F>>,
    pad: &LayerProof<W, F>,
    transcript: &mut Transcript,
    g_binding: &[ElementOf<F>],
    alpha: &ElementOf<F>,
    beta: &ElementOf<F>,
    claims: [ElementOf<F>; 2],
    f: &F,
) -> (
    LayerProof<W, F>,
    Bindings<W, F>,
    [ElementOf<F>; 2],
    ElementOf<F>,
) {
    use std::rc::Rc;
    let logw = clr.logw();
    let nw = clr.nw();
    assert!(crate::sane_logw(logw), "logw must be sane");
    let width = nw.max(1);
    assert!(width as u64 <= (1u64 << logw));
    assert!(wires.len() <= width, "witness exceeds layer width");
    wires.resize(width, f.zero());
    let mut hquad = crate::hquad::HQuad::from_g_binding(clr, constants, g_binding, beta, f);
    let shared_wires = Rc::new(wires);
    let mut w = [shared_wires.clone(), shared_wires];
    let mut qw = vec![f.zero(); width];
    let mut challenges = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut round_polys = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
    let mut sum = claims[0].clone();
    f.fma(&mut sum, alpha, &claims[1]);
    let one = f.one();
    for (hand, round) in crate::SumcheckOrder::RoundMajor.rounds(logw) {
        let n = w[hand].len();
        qw[..n].fill(f.zero());
        for (hc, vc) in hquad.hc.iter().zip(&hquad.vc) {
            f.fma(
                &mut qw[hc.h[hand] as usize],
                vc,
                &w[1 - hand][hc.h[1 - hand] as usize],
            );
        }
        let evaluations = quad_round_poly(n, &qw[..n], &w[hand], &sum, &one, f);
        let challenge = sample_round_challenge(
            transcript,
            &evaluations,
            &pad.hp[hand][round],
            &mut round_polys[hand],
            &mut challenges[hand],
            f,
        );
        sum = evaluations.eval_lagrange(&challenge, f);
        if let Some(values) = Rc::get_mut(&mut w[hand]) {
            crate::dense::bind(values, &challenge, f);
        } else {
            w[hand] = Rc::new(crate::dense::bind_out_of_place(&w[hand], &challenge, f));
        }
        hquad.bind_h(&challenge, hand, f);
    }
    let next_claims = [
        crate::dense::as_scalar::<W, F>(&w[0]),
        crate::dense::as_scalar::<W, F>(&w[1]),
    ];
    let quad_scalar = if hquad.hc.is_empty() {
        f.zero()
    } else {
        hquad.scalar()
    };
    finish_layer(
        logw,
        nw,
        challenges,
        round_polys,
        next_claims,
        quad_scalar,
        sum,
        pad,
        transcript,
        f,
    )
}

#[allow(clippy::too_many_arguments)]
fn finish_layer<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    logw: usize,
    nw: usize,
    challenges: [Vec<ElementOf<F>>; 2],
    round_polys: [Vec<crate::proof::RoundPoly<W, F>>; 2],
    next_claims: [ElementOf<F>; 2],
    quad_scalar: ElementOf<F>,
    sum: ElementOf<F>,
    pad: &LayerProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> (
    LayerProof<W, F>,
    Bindings<W, F>,
    [ElementOf<F>; 2],
    ElementOf<F>,
) {
    let mut expected_sum = f.mulf(&next_claims[0], &next_claims[1]);
    f.mul(&mut expected_sum, &quad_scalar);
    assert_eq!(
        sum, expected_sum,
        "reconstructed sum does not match expected"
    );

    let mut proof_claims = next_claims.clone();
    f.sub(&mut proof_claims[0], &pad.claims[0]);
    f.sub(&mut proof_claims[1], &pad.claims[1]);
    transcript.end_layer(&proof_claims, f);
    (
        LayerProof {
            hp: round_polys,
            claims: proof_claims,
        },
        Bindings {
            logv: logw,
            nv: nw,
            challenges,
        },
        next_claims,
        quad_scalar,
    )
}

/// Absorbs the unpadded round polynomial into the transcript after applying ZK padding,
/// samples the round challenge, and records the padded polynomial and challenge.
#[inline]
fn sample_round_challenge<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    transcript: &mut Transcript,
    unpadded_poly: &Poly<3, W, F>,
    pad_poly: &crate::proof::RoundPoly<W, F>,
    round_polys: &mut Vec<crate::proof::RoundPoly<W, F>>,
    challenges: &mut Vec<ElementOf<F>>,
    f: &F,
) -> ElementOf<F> {
    let poly_padded = unpadded_poly.to_wire().sub(pad_poly, f);
    let round_challenge = transcript.round(&poly_padded, f);
    round_polys.push(poly_padded);
    challenges.push(round_challenge.clone());
    round_challenge
}

/// Evaluates the quad round polynomial of degree 2 (represented
/// by 3 evaluation points) for the current sumcheck prover round.
///
/// Directly computes the evaluations [g(0), g(1), g(2)] without intermediate
/// monomial or Newton conversions.
#[inline]
fn quad_round_poly<const W: usize, F: InterpolationField<W>>(
    num_variables: usize,
    qw: &[ElementOf<F>],
    witness_values: &[ElementOf<F>],
    sum: &ElementOf<F>,
    scale: &ElementOf<F>,
    f: &F,
) -> Poly<3, W, F> {
    let num_pairs = num_variables / 2;
    let mut accum_a0 = f.zero_accum();
    let mut accum_a2 = f.zero_accum();

    for i in 0..num_pairs {
        let idx = 2 * i;
        f.mac(&mut accum_a0, &qw[idx], &witness_values[idx]);
        let dqw = f.subf(&qw[idx + 1], &qw[idx]);
        let dw = f.subf(&witness_values[idx + 1], &witness_values[idx]);
        f.mac(&mut accum_a2, &dqw, &dw);
    }

    if !num_variables.is_multiple_of(2) {
        let last = num_variables - 1;
        f.mac(&mut accum_a0, &qw[last], &witness_values[last]);
        f.mac(&mut accum_a2, &qw[last], &witness_values[last]);
    }

    let a0 = f.mulf(&f.accum_reduce(&accum_a0), scale);
    let a2 = f.mulf(&f.accum_reduce(&accum_a2), scale);

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
