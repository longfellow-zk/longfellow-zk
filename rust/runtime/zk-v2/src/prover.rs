// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prepare circuit witnesses, reduce sumcheck and packing, then open Polygero.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        polygero::{JointPolygeroParam, JointPolygeroProver, LinearStatement, PolygeroConfig},
        proto::polygero::PolygeroCommitment,
        random::{RandomEngine, Transcript},
        sumcheck_v2::{self, SumcheckProof, TranscriptSumcheck},
        zk_v2::{
            commitment::PackingState,
            context::private_input_count,
            joint::{CircuitParticipant, CircuitProof},
            CircuitInput, ZkContext, ZkProof, ZkProofGeometry,
        },
    },
};

/// Private masks needed to reduce one circuit after the shared commitment.
pub struct CircuitState<const W: usize, F: ZkField<W> + PackingField> {
    pads: SumcheckProof<W, F>,
    packing: PackingState<F::E>,
    id: [u8; 32],
    config: PolygeroConfig,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Validate and pack typed inputs before sampling any masks. The returned
    /// witness belongs in the corresponding position of the Polygero tuple.
    pub fn prepare(
        &self,
        private: &[CircuitInput<F>],
        rng: &mut impl RandomEngine,
    ) -> Result<(CircuitState<W, F>, Vec<F::E>), String> {
        let inputs = self.backend.prepare_inputs(private)?;
        let (pads, suffix) =
            sumcheck_v2::sample_pads(&self.geometry.sc_geom, rng, self.backend.parameters.field());
        let (packing, witness) = self.backend.prepare(inputs, suffix, rng);
        Ok((
            CircuitState {
                pads,
                packing,
                id: self.id,
                config: self.config,
            },
            witness,
        ))
    }
    /// The resulting affine statement is authenticated only when the caller
    /// completes the shared Polygero proof against the original commitment.
    /// Continue the transcript used for that commitment. All participants must
    /// finish this reduction before the joint backend samples its challenges.
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        private: Vec<CircuitInput<F>>,
        state: CircuitState<W, F>,
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
        validate_inputs(circuit, public, &private)?;
        if circuit.id != self.id || state.id != self.id || state.config != self.config {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        state
            .pads
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        let extension = self.backend.parameters.extension();
        let public = extension.input_elements(ctx.f, public);
        let private = extension.into_input_elements(ctx.f, private);
        let inputs = prepare_inputs(&public, private);
        t.write_sumcheck_statement(circuit, &public, ctx.f);
        let (sumcheck_proof, constraints) =
            sumcheck_v2::evaluate_and_prove(inputs, &state.pads, circuit, t, ctx.f)?;
        let pad_layout = self
            .geometry
            .sc_geom
            .pad_layout(self.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile_packed(
            constraints,
            &pad_layout,
            &public,
            &self.backend.layout,
            ctx.f,
        )?;
        let (packing, statement) =
            self.backend
                .prove::<W>(state.packing, statement, &self.id, t)?;
        Ok((
            CircuitProof {
                sumcheck_proof,
                packing,
            },
            statement,
        ))
    }
}

pub struct ZkProver<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) circuit: Circuit<F>,
    config: PolygeroConfig,
}
pub struct ZkProverCommitment<const W: usize, F: ZkField<W> + PackingField> {
    state: CircuitState<W, F>,
    participant: CircuitParticipant<W, F>,
    polygero: JointPolygeroProver<(Vec<Vec<F::E>>, ())>,
    commitment: PolygeroCommitment,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkProver<W, F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig) -> Self {
        Self { circuit, config }
    }
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine>(
        &self,
        private: &[CircuitInput<F>],
        ctx: &ZkContext<'_, W, F, D>,
        t: &mut Transcript,
        rng: &mut R,
    ) -> Result<(ZkProverCommitment<W, F>, ZkProofGeometry), String> {
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let participant = CircuitParticipant::new(&self.circuit, self.config, ctx)?;
        let (state, witness) = participant.prepare(private, rng)?;
        let joint = JointPolygeroParam::new((participant.participant(ctx)?, ()))
            .map_err(|e| e.to_string())?;
        participant.bind(t);
        let (polygero, commitment) = JointPolygeroProver::commit(&joint, (witness, ()), t, rng)
            .map_err(|e| e.to_string())?;
        let geometry = participant.geometry();
        Ok((
            ZkProverCommitment {
                state,
                participant,
                polygero,
                commitment,
            },
            geometry,
        ))
    }
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        public: &[CircuitInput<F>],
        private: Vec<CircuitInput<F>>,
        committed: ZkProverCommitment<W, F>,
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<ZkProof<W, F>, String> {
        if committed.participant.config != self.config {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        let (circuit, statement) =
            committed
                .participant
                .prove(&self.circuit, public, private, committed.state, t, ctx)?;
        let joint = JointPolygeroParam::new((committed.participant.participant(ctx)?, ()))
            .map_err(|e| e.to_string())?;
        let com_proof = committed
            .polygero
            .prove(&joint, &(statement, ()), t)
            .map_err(|e| e.to_string())?;
        Ok(ZkProof {
            com: committed.commitment,
            sumcheck_proof: circuit.sumcheck_proof,
            packing: circuit.packing,
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
