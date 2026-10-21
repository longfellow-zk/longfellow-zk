// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    hquad::HQuad,
    proof::{SumcheckProof, SumcheckProofGeometry},
    transcript::TranscriptSumcheck,
    verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData},
    LagrangeBasis,
};
use runtime_algebra::{ElementOf, InterpolationField, SupportsSampling};
use runtime_random::{RandomEngine, Transcript};

/// Independently derive local verifier data after the statement has been bound.
/// Success validates proof shape and derives coefficients; it does not establish
/// acceptance. Only scalar data and the final dense input weights are retained.
pub fn derive_verifier_data<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    circuit: &core_proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<VerifierData<ElementOf<F>>, String> {
    proof
        .validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    let (_, initial) = transcript.begin_circuit(f);
    let mut points = [initial.clone(), initial];
    let mut logv = circuit.raw.logv;
    let mut nv = circuit.raw.noutput;
    let basis = LagrangeBasis::new(f);
    let mut layers = Vec::with_capacity(proof.layers.len());
    for (layer, messages) in circuit.raw.layers.iter().zip(&proof.layers) {
        let (alpha, beta) = transcript.begin_layer(f);
        let mut next_points = [
            Vec::with_capacity(layer.logw()),
            Vec::with_capacity(layer.logw()),
        ];
        let mut rounds = [
            Vec::with_capacity(layer.logw()),
            Vec::with_capacity(layer.logw()),
        ];
        for round in 0..layer.logw() {
            for hand in 0..2 {
                let challenge = transcript.round(&messages.hp[hand][round], f);
                rounds[hand].push(RoundCoefficients::new(&basis, &challenge, f));
                next_points[hand].push(challenge);
            }
        }
        let bound_quad = {
            let mut quad = HQuad::bind_g(
                layer,
                &circuit.raw.constants,
                logv,
                nv,
                &points[0],
                &points[1],
                &alpha,
                &beta,
                f,
            );
            for (right, left) in next_points[0].iter().zip(&next_points[1]) {
                quad.bind_h(right, 0, f);
                quad.bind_h(left, 1, f);
            }
            quad.scalar()
        };
        transcript.end_layer(&messages.claims, f);
        points = next_points;
        logv = layer.logw();
        nv = layer.nw();
        layers.push(LayerVerifierData {
            rounds,
            alpha,
            bound_quad,
        });
    }
    let input_alpha = transcript.elt_field(f);
    let input_weights = crate::eq::eq2(
        logv,
        circuit.raw.ninput,
        &points[0],
        &points[1],
        &input_alpha,
        f,
    );
    Ok(VerifierData {
        layers,
        input_alpha,
        input_weights,
    })
}

/// Numerical verification with revealed inputs and pads, using the same logical
/// relations that production ZK verification compiles into Ligero constraints.
pub fn verify_core<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    inputs: Vec<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(), String> {
    pad.validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    let data = derive_verifier_data(circuit, proof, transcript, f)?;
    let relations = crate::symbolic::verify(proof, data, f)?;
    let residuals = relations.evaluate(&inputs, pad, f)?;
    if residuals[..proof.layers.len()]
        .iter()
        .any(|value| !f.is_zero(value))
    {
        return Err("got != claim (layer)".into());
    }
    if !f.is_zero(residuals.last().expect("input relation always exists")) {
        return Err("input claim mismatch".into());
    }
    Ok(())
}

pub fn verify<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    inputs: Vec<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(), String> {
    if inputs.len() < circuit.raw.npublic_input {
        return Err("public input length mismatch".into());
    }
    transcript.write_sumcheck_statement(circuit, &inputs[..circuit.raw.npublic_input], f);
    verify_core(inputs, pad, circuit, proof, transcript, f)
}
