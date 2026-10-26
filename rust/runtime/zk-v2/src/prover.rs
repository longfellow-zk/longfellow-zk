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

//! Prove a circuit by committing its private inputs and sumcheck pads first.
//!
//! `commit` samples the pads and commits the vector [private inputs, pads,
//! pad products] with Polygero. The caller can then derive public inputs from
//! the transcript, as the mdoc application does after committing both circuits.
//!
//! `prove` consumes that commitment state. It binds the public inputs, evaluates
//! the circuit and runs numerical sumcheck. It samples the statement identifier
//! before compiling the resulting symbolic constraints into A*w+b=0.
//! Finally Polygero proves those constraints against
//! the original commitment. Pads and symbolic constraints end at the sumcheck
//! phase; the encoded witness and Merkle tree end when this invocation returns.
use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::{ElementOf, EvaluationDomain, Subfield, ZkField},
        polygero::{PolygeroConfig, PolygeroLinearTerm, PolygeroProver},
        proto::Digest,
        random::{RandomEngine, Transcript},
        sumcheck_v2::{self, SumcheckProof, SumcheckProofGeometry, TranscriptSumcheck},
        zk_v2::{
            constraint_compiler,
            context::{prepare_layout, private_input_count},
            ZkContext, ZkProof, ZkProofGeometry,
        },
    },
};

/// Trusted circuit and fixed Polygero configuration, reusable across invocations.
pub struct ZkProver<const W: usize, F: ZkField<W>> {
    pub(super) circuit: Circuit<F>,
    config: PolygeroConfig,
}

/// Private state for one committed invocation, consumed by `ZkProver::prove`.
pub struct ZkProverCommitment<const W: usize, F: ZkField<W>> {
    pads: SumcheckProof<W, F>,
    polygero: PolygeroProver<W, F>,
    commitment: crate::runtime::proto::polygero::PolygeroCommitment,
}

impl<const W: usize, F: ZkField<W>> ZkProver<W, F> {
    /// Select the circuit and commitment dimensions; commitment validates the domain.
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig) -> Self {
        Self { circuit, config }
    }

    /// Sample sumcheck pads and commit them after the private circuit inputs.
    /// Each layer's final pads p_A,p_B also have a committed product p_A*p_B.
    /// Fix those product constraints now, before sumcheck chooses any challenges.
    #[allow(clippy::too_many_arguments)]
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine, SF: Subfield<E = ElementOf<F>>>(
        &self,
        private_inputs: &[ElementOf<F>],
        ctx: &ZkContext<'_, W, F, D>,
        transcript: &mut Transcript,
        rng: &mut R,
        sf: &SF,
    ) -> Result<(ZkProverCommitment<W, F>, ZkProofGeometry), String> {
        let nprivate = private_input_count(&self.circuit);
        if private_inputs.len() != nprivate {
            return Err("witness length mismatch".into());
        }

        // Circuit indices include the public prefix; Polygero commits only the suffix.
        let subfield_boundary = self
            .circuit
            .raw
            .subfield_boundary
            .saturating_sub(self.circuit.raw.npublic_input);

        let (geom, param) = prepare_layout(&self.circuit, self.config, ctx)?;
        let (pads, pad_values) = sumcheck_v2::sample_pads(&geom.sc_geom, rng, ctx.f);

        let mut witness = Vec::with_capacity(nprivate + pad_values.len());
        witness.extend_from_slice(private_inputs);
        witness.extend(pad_values);

        let (polygero, commitment) = PolygeroProver::commit(
            subfield_boundary,
            witness,
            param,
            transcript,
            ctx.domain,
            rng,
            ctx.f,
            sf,
        )
        .map_err(|e| e.to_string())?;
        Ok((
            ZkProverCommitment {
                pads,
                polygero,
                commitment,
            },
            geom,
        ))
    }

    /// Consume one commitment, prove sumcheck, then prove its compiled constraints.
    /// Public inputs are borrowed; private inputs become the numerical witness.
    /// The returned proof contains only public messages and authenticated openings.
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        public_inputs: &[ElementOf<F>],
        private_inputs: Vec<ElementOf<F>>,
        committed: ZkProverCommitment<W, F>,
        transcript: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<ZkProof<W, F>, String> {
        validate_inputs(&self.circuit, public_inputs, &private_inputs)?;
        let ZkProverCommitment {
            pads,
            polygero,
            commitment,
        } = committed;
        #[cfg(feature = "bench-profile")]
        let mut profile =
            crate::util::profile::Timer::new(format!("zk{W}.prover.gkr_and_constraints"));
        let (sumcheck_proof, a, b, statement) =
            self.prove_sumcheck(public_inputs, private_inputs, pads, transcript, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next(format!("zk{W}.prover.backend_and_cleanup"));
        let com_proof = polygero
            .prove(&b, transcript, &a, &statement, ctx.domain, ctx.f)
            .map_err(|e| e.to_string())?;

        Ok(ZkProof {
            com: commitment,
            sumcheck_proof,
            com_proof,
        })
    }

    /// Run sumcheck, sample its statement identifier, then compile the constraints.
    /// This phase owns the private inputs and pads. Their storage and the
    /// symbolic expressions are released before the Polygero response is built.
    fn prove_sumcheck(
        &self,
        public_inputs: &[F::E],
        private_inputs: Vec<F::E>,
        pads: SumcheckProof<W, F>,
        transcript: &mut Transcript,
        f: &F,
    ) -> Result<
        (
            SumcheckProof<W, F>,
            Vec<PolygeroLinearTerm<F::E>>,
            Vec<F::E>,
            Digest,
        ),
        String,
    > {
        let geometry = SumcheckProofGeometry::from_circuit(&self.circuit);
        pads.validate(&geometry)
            .map_err(|error| error.to_string())?;
        let inputs = prepare_inputs(public_inputs, private_inputs);
        transcript.write_sumcheck_statement(&self.circuit, public_inputs, f);
        let w_layers = sumcheck_v2::eval_circuit(inputs, &self.circuit, f)
            .map_err(|e| format!("eval_circuit failed: {e}"))?;
        let (proof, constraints) =
            sumcheck_v2::prove_core(w_layers, &pads, &self.circuit, transcript, f);
        let statement = super::transcript::statement_digest(transcript);
        let layout = geometry.pad_layout(private_input_count(&self.circuit));
        let (a, b) = constraint_compiler::compile(&constraints, &layout, public_inputs, f)?;
        Ok((proof, a, b, statement))
    }
}

/// Reject wrong input lengths before changing the proof transcript.
fn validate_inputs<F: crate::core::algebra::SerializableField>(
    circuit: &Circuit<F>,
    public: &[F::E],
    private: &[F::E],
) -> Result<(), String> {
    if public.len() != circuit.raw.npublic_input {
        return Err("public inputs length mismatch".into());
    }
    if private.len() != private_input_count(circuit) {
        return Err("witness length mismatch".into());
    }
    Ok(())
}

/// Assemble the public prefix and private suffix for circuit evaluation.
/// Move private elements into the combined vector; copy only the borrowed prefix.
fn prepare_inputs<E: Clone>(public: &[E], private: Vec<E>) -> Vec<E> {
    let mut inputs = Vec::with_capacity(public.len() + private.len());
    inputs.extend_from_slice(public);
    inputs.extend(private);
    inputs
}

#[cfg(test)]
#[path = "../tests/prover.rs"]
mod tests;
