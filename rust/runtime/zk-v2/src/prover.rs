// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Commit inputs and sumcheck pads, reduce packing, then authenticate all equations.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        polygero::PolygeroConfig,
        random::{RandomEngine, Transcript},
        sumcheck_v2::{self, SumcheckProof, SumcheckProofGeometry, TranscriptSumcheck},
        zk_v2::{
            commitment::CommitmentState,
            context::{prepare_layout, private_input_count},
            CircuitInput, ZkContext, ZkProof, ZkProofGeometry,
        },
    },
};

pub struct ZkProver<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) circuit: Circuit<F>,
    config: PolygeroConfig,
}
pub struct ZkProverCommitment<const W: usize, F: ZkField<W> + PackingField> {
    pads: SumcheckProof<W, F>,
    inner: CommitmentState<W, F, <F as PackingField>::Packing>,
    circuit_id: [u8; 32],
    config: PolygeroConfig,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkProver<W, F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig) -> Self {
        Self { circuit, config }
    }
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkProver<W, F> {
    /// Validate the input domain before sampling masks or advancing the transcript.
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine>(
        &self,
        private: &[CircuitInput<F>],
        ctx: &ZkContext<'_, W, F, D>,
        transcript: &mut Transcript,
        rng: &mut R,
    ) -> Result<(ZkProverCommitment<W, F>, ZkProofGeometry), String> {
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let (geometry, param, backend) =
            prepare_layout(&self.circuit, self.config, ctx.f.packing_extension(), ctx)?;
        let inputs = backend.prepare_inputs(private)?;
        let (pads, suffix) = sumcheck_v2::sample_pads(&geometry.sc_geom, rng, ctx.f);
        let inner = backend.commit(
            inputs,
            suffix,
            param,
            &self.circuit.id,
            transcript,
            rng,
            ctx.domain,
        )?;
        Ok((
            ZkProverCommitment {
                pads,
                inner,
                circuit_id: self.circuit.id,
                config: self.config,
            },
            geometry,
        ))
    }
    /// Run ordinary sumcheck, reduce its input claim, and authenticate against the same root.
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        public: &[CircuitInput<F>],
        private: Vec<CircuitInput<F>>,
        committed: ZkProverCommitment<W, F>,
        transcript: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<ZkProof<W, F>, String> {
        validate_inputs(&self.circuit, public, &private)?;
        if committed.circuit_id != self.circuit.id || committed.config != self.config {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        let geometry = SumcheckProofGeometry::from_circuit(&self.circuit);
        committed
            .pads
            .validate(&geometry)
            .map_err(|e| e.to_string())?;
        let extension = committed.inner.backend.parameters.extension();
        let public = extension.input_elements(ctx.f, public);
        let private = extension.into_input_elements(ctx.f, private);
        let inputs = prepare_inputs(&public, private);
        transcript.write_sumcheck_statement(&self.circuit, &public, ctx.f);
        let (sumcheck_proof, constraints) = sumcheck_v2::evaluate_and_prove(
            inputs,
            &committed.pads,
            &self.circuit,
            transcript,
            ctx.f,
        )?;
        let pad_layout = geometry.pad_layout(committed.inner.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile_packed(
            constraints,
            &pad_layout,
            &public,
            &committed.inner.backend.layout,
            ctx.f,
        )?;
        let com = committed.inner.commitment.clone();
        let (packing, com_proof) =
            committed
                .inner
                .prove(statement, &self.circuit.id, transcript, ctx.domain)?;
        Ok(ZkProof {
            com,
            sumcheck_proof,
            packing,
            com_proof,
        })
    }
}
fn validate_inputs<F: crate::core::algebra::SerializableField, I>(
    circuit: &Circuit<F>,
    public: &[I],
    private: &[I],
) -> Result<(), String> {
    if public.len() != circuit.raw.npublic_input {
        return Err("public inputs length mismatch".into());
    }
    if private.len() != private_input_count(circuit) {
        return Err("witness length mismatch".into());
    }
    Ok(())
}
fn prepare_inputs<E: Clone>(public: &[E], private: Vec<E>) -> Vec<E> {
    let mut inputs = Vec::with_capacity(public.len() + private.len());
    inputs.extend_from_slice(public);
    inputs.extend(private);
    inputs
}
#[cfg(test)]
#[path = "../tests/prover.rs"]
mod tests;
