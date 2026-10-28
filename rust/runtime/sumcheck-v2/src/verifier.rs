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

//! Revealed-pad sumcheck v2 verifier for testing and protocol diagnostics.
//!
//! Reconstruct the public challenges and symbolic constraints from the masked
//! proof, then substitute the supplied input vector and secret pads. Each
//! constraint becomes a field residual that must be zero.
//!
//! For a layer's final round claim C, the two messages hide A and B:
//!
//! ```text
//! A = m_A + p_A,  B = m_B + p_B,
//! E = C - m_A*m_B - m_B*p_A - m_A*p_B,
//! layer_residual = E - p_A*p_B = C - A*B.
//! ```
//!
//! The symbolic builder stores only the affine expression E. Evaluate it with
//! the revealed pads, then subtract the omitted product. After the last layer,
//! also check input_residual = input_claim - sum_i input_weights[i]*inputs[i].
//!
//! This diagnostic verifier requires complete inputs and pads and is not used
//! in production. [`crate::runtime::zk_v2::ZkVerifier`] compiles the same symbolic
//! constraints and checks them through Polygero while keeping those values hidden.

use super::{
    symbolic::{Constraints, Pad, PadExpression},
    RoundPoly,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{blas, ElementOf, RuntimeField, SupportsSampling},
        random::Transcript,
        sumcheck_v2::{
            derive_constraints, SumcheckProof, SumcheckProofGeometry, TranscriptSumcheck,
        },
    },
};

/// Bind the circuit ID and public-input prefix, then check with revealed pads.
/// `inputs` contains the complete circuit input vector in circuit wire order;
/// `pads` has the proof's shape and stores the secret pads instead of messages.
pub fn verify<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    inputs: Vec<ElementOf<F>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(), String> {
    if inputs.len() < circuit.raw.npublic_input {
        return Err("public input length mismatch".into());
    }
    transcript.write_sumcheck_statement(circuit, &inputs[..circuit.raw.npublic_input], f);
    verify_core(inputs, pads, circuit, proof, transcript, f)
}

/// Check sumcheck numerically after the caller has bound the public statement.
/// Reconstruct constraints from the masked transcript, substitute the inputs
/// and pads, then check the layer residuals followed by the final input residual.
pub fn verify_core<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    inputs: Vec<ElementOf<F>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::circuit::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(), String> {
    pads.validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    if inputs.len() != circuit.raw.ninput {
        return Err("single-hand input width mismatch".into());
    }
    let constraints = derive_constraints(circuit, proof, transcript, f)?;
    let residuals = constraints.residuals(&inputs, pads, f)?;
    let (input_residual, layer_residuals) = residuals
        .split_last()
        .expect("input constraint always exists");
    if !blas::equal0(layer_residuals, f) {
        return Err("single-hand terminal product mismatch".into());
    }
    if !f.is_zero(input_residual) {
        return Err("single-hand input claim mismatch".into());
    }
    Ok(())
}

impl<E: Clone> Constraints<E> {
    /// Return the numerical residuals in circuit output-to-input order.
    /// Each layer contributes C - A*B; the last residual connects the final
    /// symbolic claim to the weighted circuit inputs. This order also matches
    /// the linear constraints produced by the ZK constraint compiler.
    pub(crate) fn residuals<const W: usize, F: RuntimeField<W, E = E> + SerializableField>(
        &self,
        inputs: &[E],
        pads: &SumcheckProof<W, F>,
        f: &F,
    ) -> Result<Vec<E>, String> {
        if pads.layers.len() != self.layers.len() || inputs.len() != self.input_weights.len() {
            return Err("sumcheck constraint input shape mismatch".into());
        }
        let mut residuals = Vec::with_capacity(self.layers.len() + 1);
        for (expression, layer_pads) in self.layers.iter().zip(&pads.layers) {
            // The expression stores E = C - m_A*m_B - m_B*p_A - m_A*p_B.
            // Restore its omitted quadratic term to obtain C - A*B.
            let mut residual = expression.evaluate(pads, f)?;
            let [p_a, p_b] = &layer_pads.claims;
            f.fnms(&mut residual, p_a, p_b);
            residuals.push(residual);
        }
        // input_claim - sum_i input_weights[i]*inputs[i] = 0.
        let mut input_residual = self.input_claim.evaluate(pads, f)?;
        f.sub(
            &mut input_residual,
            &blas::dot(&self.input_weights, inputs, f),
        );
        residuals.push(input_residual);
        Ok(residuals)
    }
}

impl<E: Clone> PadExpression<E> {
    /// Substitute pads into the sparse affine expression
    /// constant + sum_{(pad,k) in terms} k*pad_value(pad).
    fn evaluate<const W: usize, F: RuntimeField<W, E = E> + SerializableField>(
        &self,
        pads: &SumcheckProof<W, F>,
        f: &F,
    ) -> Result<E, String> {
        let mut value = self.constant.clone();
        for (pad, k) in &self.terms {
            f.fma(&mut value, k, pad_value(*pad, pads)?);
        }
        Ok(value)
    }
}

/// Resolve a symbolic pad coordinate in the revealed proof-shaped pad array.
/// Round slots 0,1 hold the pads for c0,c1; claim slots 0,1 hold p_A,p_B.
fn pad_value<const W: usize, F: SerializableField>(
    pad: Pad,
    pads: &SumcheckProof<W, F>,
) -> Result<&F::E, String> {
    match pad {
        Pad::Round { layer, round, slot } => pads
            .layers
            .get(layer)
            .and_then(|layer_pads| layer_pads.rounds.get(round))
            .and_then(|RoundPoly { coefficients }| coefficients.get(slot)),
        Pad::Claim { layer, slot } => pads
            .layers
            .get(layer)
            .and_then(|layer_pads| layer_pads.claims.get(slot)),
    }
    .ok_or_else(|| "sumcheck constraint pad shape mismatch".into())
}
