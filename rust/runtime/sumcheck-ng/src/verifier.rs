// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    eq::{next_weights, weights},
    eval::assertion_outputs,
    proof::{SumcheckProof, SumcheckProofGeometry},
    transcript::{assertion_weights, begin, combine},
    verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData},
    wiring::contract,
    LagrangeBasis, TranscriptSumcheck,
};
use runtime_algebra::{ElementOf, InterpolationField, SupportsSampling};
use runtime_random::Transcript;

/// Independently derive constraint-building data from the public circuit and proof.
/// The caller must first bind the statement. This consumes the sumcheck transcript
/// once and retains no intermediate dense weights or raw round challenges.
/// Success validates shape and derives data; it does not check acceptance equations.
pub fn derive_verifier_data<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    circuit: &core_proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<VerifierData<ElementOf<F>>, String> {
    proof
        .validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    let basis = LagrangeBasis::new(f);
    let mut lambda = begin(circuit, transcript, f);
    let mut layers = Vec::with_capacity(proof.layers.len());
    for (index, (layer, messages)) in circuit.raw.layers.iter().zip(&proof.layers).enumerate() {
        let assertions = {
            let outputs = assertion_outputs(layer, &circuit.raw.constants, lambda.len(), f)?;
            assertion_weights(&outputs, index, transcript, f)
        };
        let mut point = Vec::with_capacity(layer.logw());
        let mut rounds = Vec::with_capacity(layer.logw());
        for message in &messages.rounds {
            let challenge = transcript.round(message, f);
            rounds.push(RoundCoefficients::new(&basis, &challenge, f));
            point.push(challenge);
        }
        let chi = weights(layer.logw(), layer.nw(), &point, f);
        let mu = contract(
            layer,
            &circuit.raw.constants,
            &lambda,
            &assertions,
            &chi,
            1,
            f,
        );
        let alpha = combine(&messages.claims, transcript, f);
        lambda = next_weights(chi, &mu, &alpha, f);
        layers.push(LayerVerifierData { rounds, alpha });
    }
    if lambda.len() != circuit.raw.ninput {
        return Err("single-hand input width mismatch".into());
    }
    Ok(VerifierData {
        layers,
        input_weights: lambda,
    })
}

/// Numerical verification with revealed inputs and pads, for testing.
/// Production verification derives data, builds these same symbolic relations,
/// and checks their compilation through zk-ng and Ligero.
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
    if inputs.len() != circuit.raw.ninput {
        return Err("single-hand input width mismatch".into());
    }
    let data = derive_verifier_data(circuit, proof, transcript, f)?;
    let relations = crate::symbolic::verify(proof, data, f)?;
    let residuals = relations.evaluate(&inputs, pad, f)?;
    if residuals[..proof.layers.len()]
        .iter()
        .any(|value| !f.is_zero(value))
    {
        return Err("single-hand terminal product mismatch".into());
    }
    if !f.is_zero(residuals.last().expect("input relation always exists")) {
        return Err("single-hand input claim mismatch".into());
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
