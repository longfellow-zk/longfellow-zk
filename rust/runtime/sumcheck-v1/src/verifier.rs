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

//! Reconstruct v1 sumcheck constraints, or check them with revealed inputs and pads.
//!
//! `derive_verifier_data` replays the fixed transcript, obtains each round's
//! interpolation weights, and binds QUAD at both final witness points. It returns
//! public scalar data and the final input weights. Production `zk_v1::ZkVerifier`
//! turns these into symbolic constraints and proves them through Ligero.
//!
//! `verify` and `verify_core` are numerical checks for callers that possess the
//! complete inputs and pads. They evaluate those same constraints directly.
use crate::runtime::{
    algebra::{ElementOf, InterpolationField, SupportsSampling},
    random::{RandomEngine, Transcript},
    sumcheck_v1::{
        hquad::HQuad,
        proof::{SumcheckProof, SumcheckProofGeometry},
        transcript::TranscriptSumcheck,
        verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData},
        LagrangeBasis,
    },
};

/// Independently derive local verifier data after the statement has been bound.
/// Success validates proof shape and derives coefficients; it does not establish
/// acceptance. Only scalar data and the final dense input weights are retained.
pub fn derive_verifier_data<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    circuit: &crate::core::proto::circuit::Circuit<F>,
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
        let mut points_next = [
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
                points_next[hand].push(challenge);
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
            for (right, left) in points_next[0].iter().zip(&points_next[1]) {
                quad.bind_h(right, 0, f);
                quad.bind_h(left, 1, f);
            }
            quad.scalar()
        };
        transcript.end_layer(&messages.claims, f);
        points = points_next;
        logv = layer.logw();
        nv = layer.nw();
        layers.push(LayerVerifierData {
            rounds,
            alpha,
            bound_quad,
        });
    }
    let input_alpha = transcript.elt_field(f);
    let input_weights = crate::runtime::sumcheck_v1::eq::eq2(
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
pub fn verify_core<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    inputs: Vec<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(), String> {
    pad.validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    let data = derive_verifier_data(circuit, proof, transcript, f)?;
    let relations = crate::runtime::sumcheck_v1::symbolic::verify(proof, data, f)?;
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

/// Bind the public statement, then check the proof against revealed witness data.
pub fn verify<const W: usize, F: InterpolationField<W> + SupportsSampling>(
    inputs: Vec<ElementOf<F>>,
    pad: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
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
