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

//! Derive constraints on hidden inputs and pads from the public sumcheck transcript.
//!
//! Starting at the circuit outputs, a holds the weights of the current claim.
//! For each layer, absorb the masked round coefficients to sample a point u,
//! then absorb the final-claim pair to sample its combination challenge alpha.
//! The public circuit determines the next weights:
//!
//! ```text
//! m_l[i] = product_j u[j]^i_j,
//! q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] m_l[l],
//! a_next[r] = m_l[r] + alpha*q_r[r].
//! ```
//!
//! These weights express the next claim A + alpha*B as a weighted sum of the
//! layer's inputs. Assertion quads use their sampled replacement coefficients.
//! After the last layer, a weights the circuit inputs. Pass it and all sampled
//! challenges to `build_constraints`, which tracks the hidden claims as affine
//! expressions in the pads and forms the layer and input constraints.
//!
//! [`crate::runtime::zk_v2::ZkVerifier`] compiles the resulting constraints and
//! checks them through Polygero. Deriving constraints alone does not check them.

use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{ElementOf, RuntimeField, SupportsSampling},
        random::Transcript,
        sumcheck_v2::{
            proof::{LayerProof, SumcheckProof, SumcheckProofGeometry},
            quad::weights_next_affine,
            symbolic::{build_constraints, Constraints, LayerChallenges},
            transcript::{assertion_weights, begin, end_layer, round_challenge},
        },
    },
};

/// Reconstruct each circuit layer's challenges and input weights, then build
/// the symbolic constraints. The caller must have absorbed the public statement.
/// Validate message counts before advancing the transcript.
pub(crate) fn derive_constraints<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuit: &Circuit<F>,
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<Constraints<ElementOf<F>>, String> {
    circuit.validate_v2()?;
    proof
        .validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    let mut a = begin(circuit, transcript, f);
    let mut layer_challenges = Vec::with_capacity(proof.layers.len());
    for layer_index in 0..proof.layers.len() {
        let (challenges, a_next) = layer(
            layer_index,
            &proof.layers[layer_index],
            circuit,
            &a,
            transcript,
            f,
        );
        a = a_next;
        layer_challenges.push(challenges);
    }
    if a.len() != circuit.raw.ninput {
        return Err("single-hand input width mismatch".into());
    }
    Ok(build_constraints(proof, layer_challenges, a, f))
}

/// Reconstruct one layer's challenges and return weights on its inputs.
/// The round challenges form point_l = u. Binding QUAD at u expresses B as
/// sum_r q_r[r]*W[r], while A = sum_r m_l[r]*W[r]. Their combined claim therefore
/// uses a_next[r] = m_l[r] + alpha*q_r[r]. All these weights are public.
fn layer<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    layer_index: usize,
    proof: &LayerProof<W, F>,
    circuit: &Circuit<F>,
    a: &[F::E],
    transcript: &mut Transcript,
    f: &F,
) -> (LayerChallenges<F::E>, Vec<F::E>) {
    let circuit_layer = &circuit.raw.layers[layer_index];
    let constants = &circuit.raw.constants;
    assert!(circuit_layer.nw() > 0, "sumcheck layer must contain a wire");
    let assertions = assertion_weights(circuit_layer, constants, layer_index, transcript, f);

    // Each coefficient pair is absorbed before its challenge is sampled.
    let mut point_l = Vec::with_capacity(circuit_layer.logw());
    for m in &proof.rounds {
        point_l.push(round_challenge(m, transcript, f));
    }
    // Bind both masked claims before drawing their combination challenge.
    let alpha = end_layer(&proof.claims, transcript, f);

    // The next claim is A + alpha*(B - L(u)). Its weights use only Q;
    // the symbolic builder subtracts the public linear correction separately.
    let constant = super::quad::affine_constant(circuit_layer, constants, a, f);
    let (a_next, linear) = weights_next_affine(
        circuit_layer,
        constants,
        a,
        &assertions,
        &point_l,
        &alpha,
        f,
    );
    (
        LayerChallenges {
            point_l,
            alpha,
            constant,
            linear,
        },
        a_next,
    )
}
