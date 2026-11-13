// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prepare circuit witnesses, reduce sumcheck and packing, then open Polygero.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        random::RandomEngine,
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            proto::{
                polygero::PolygeroCommitment,
                witness_selection::{FingerprintResponse, FINGERPRINTS},
            },
            sumcheck::{self, SumcheckProof, TranscriptSumcheck},
            transcript::{Transcript, TranscriptRef},
            zk::{
                context::private_input_count,
                joint::{CircuitParticipant, CircuitProof, JointParam, JointProver},
                packing_commitment::PackingState,
                split::PendingSplit,
                storage::Storage,
                CircuitInput, VirtualInputs, ZkContext, ZkProof, ZkProofGeometry,
            },
        },
    },
};

/// Owned private inputs and masks for reduction after the shared commitment.
pub struct CircuitState<const W: usize, F: ZkField<W> + PackingField> {
    private: Vec<CircuitInput<F>>,
    pads: SumcheckProof<W, F>,
    packing: PackingState<F::E>,
    id: [u8; 32],
    config: PolygeroConfig,
    additional_ids: Vec<[u8; 32]>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Own, validate and pack typed inputs before sampling any masks. The returned
    /// witness belongs in the corresponding position of the Polygero tuple.
    pub fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl RandomEngine,
    ) -> Result<(CircuitState<W, F>, Vec<F::E>), String> {
        let inputs = self.backend.prepare_inputs(&private)?;
        let (pads, suffix) =
            sumcheck::sample_pads(&self.geometry.sc_geom, rng, self.backend.parameters.field());
        let (packing, witness) = self.backend.prepare(inputs, suffix, rng);
        Ok((
            CircuitState {
                private,
                pads,
                packing,
                id: self.id,
                config: self.config,
                additional_ids: self.additional_ids.clone(),
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
        state: CircuitState<W, F>,
        t: &mut TranscriptRef<'_>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
        self.prove_circuits(circuit, public, state, &[], t, ctx)
    }
    /// Prove all supplied circuits using the private inputs owned by the state.
    /// The result contains one ordinary sumcheck and one packing reduction.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_circuits<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        state: CircuitState<W, F>,
        others: &[&Circuit<F>],
        t: &mut TranscriptRef<'_>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
        self.prove_virtual(
            circuit,
            public,
            state,
            others,
            &VirtualInputs::none(),
            t,
            ctx,
        )
    }
    /// As `prove_circuits`, appending this proof's virtual input entries to the
    /// shared input array. Their definitions are substituted, not committed.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_virtual<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        state: CircuitState<W, F>,
        others: &[&Circuit<F>],
        virtual_inputs: &VirtualInputs<F::E>,
        t: &mut TranscriptRef<'_>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
        if public.len() != circuit.raw.npublic_input {
            return Err("public inputs length mismatch".into());
        }
        self.validate_circuits(circuit, public.len(), others)?;
        virtual_inputs.validate(&self.inputs)?;
        if state.id != self.id
            || state.config != self.config
            || state.additional_ids != self.additional_ids
        {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        state
            .pads
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        let extension = self.backend.parameters.extension();
        let public = extension.input_elements(ctx.field(), public);
        let private = extension.into_input_elements(ctx.field(), state.private);
        let mut inputs = prepare_inputs(&public, private);
        let f = ctx.field();
        for v in &virtual_inputs.entries {
            let value = f.addf(&v.constant, &f.mulf(&v.coefficient, &inputs[v.source]));
            inputs.push(value);
        }
        let mut circuits = vec![circuit];
        circuits.extend_from_slice(others);
        for c in &circuits {
            t.write_sumcheck_statement(c, &public, ctx.field());
        }
        let (sumcheck_proof, constraints) =
            sumcheck::evaluate_and_prove_circuits(&circuits, inputs, &state.pads, t, ctx.field())?;
        let pad_layout = self
            .geometry
            .sc_geom
            .pad_layout(self.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile_packed(
            constraints,
            &pad_layout,
            &public,
            &self.backend.layout,
            virtual_inputs,
            ctx.field(),
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
    joint: JointProver<
        (Vec<Vec<F::E>>, ()),
        ([Vec<F::E>; FINGERPRINTS], ()),
        (FingerprintResponse<F::E>, ()),
    >,
    commitment: PolygeroCommitment,
    fingerprints: FingerprintResponse<F::E>,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkProver<W, F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig) -> Self {
        Self { circuit, config }
    }
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine>(
        &self,
        private: Vec<CircuitInput<F>>,
        ctx: &ZkContext<'_, W, F, D>,
        t: Transcript,
        rng: &mut R,
    ) -> Result<(ZkProverCommitment<W, F>, ZkProofGeometry), String> {
        let participant = CircuitParticipant::new(&self.circuit, self.config, ctx)?;
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let (state, witness) = participant.prepare(private, rng)?;
        let param = JointParam::new((participant.participant(ctx)?, ()))?;
        let (joint, commitment, (fingerprints, ())) = param.commit((witness, ()), t, rng)?;
        let geometry = ZkProofGeometry {
            circuit: participant.geometry(),
            joint_context: param.context(),
        };
        Ok((
            ZkProverCommitment {
                state,
                participant,
                joint,
                commitment,
                fingerprints,
            },
            geometry,
        ))
    }
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        public: &[CircuitInput<F>],
        mut committed: ZkProverCommitment<W, F>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(ZkProof<W, F>, Transcript), String> {
        if committed.participant.config != self.config {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        let (circuit, statement) = committed.participant.prove(
            &self.circuit,
            public,
            committed.state,
            &mut committed.joint.transcript(),
            ctx,
        )?;
        let param = JointParam::new((committed.participant.participant(ctx)?, ()))?;
        let (com_proof, transcript) = committed.joint.prove(&param, (statement, ()))?;
        Ok((
            ZkProof {
                com: committed.commitment,
                fingerprints: committed.fingerprints,
                sumcheck_proof: circuit.sumcheck_proof,
                packing: circuit.packing,
                com_proof,
            },
            transcript,
        ))
    }
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


/// Prover state of a split participant between commitment and reduction.
pub struct SplitState<const W: usize, F: ZkField<W>> {
    pads: sumcheck::SumcheckProof<W, F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    mask: Option<F::E>,
    id: [u8; 32],
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Sample pads and return the native witness `[native private inputs | R |
    /// pads]`, which is empty for pure foreign storage. `mask` is R, present
    /// exactly when some values are native.
    pub fn prepare_split(
        &self,
        private: Vec<CircuitInput<F>>,
        mask: Option<F::E>,
        rng: &mut impl RandomEngine,
    ) -> Result<(SplitState<W, F>, Vec<F::E>), String> {

        let split = self.split()?;
        if mask.is_some() != split.mask.is_some() || private.len() != self.inputs.committed() {
            return Err("split witness shape".into());
        }
        let f = self.backend.parameters.field();
        let mut values = self.backend.parameters.extension().into_input_elements(f, private);
        let (pads, suffix) = sumcheck::sample_pads(&self.geometry.sc_geom, rng, f);
        values.extend(suffix);
        let mut witness: Vec<_> = split
            .map
            .entries()
            .iter()
            .zip(&values)
            .filter(|(s, _)| matches!(s, Storage::Native(_)))
            .map(|(_, v)| v.clone())
            .collect();
        if let Some(m) = &mask {
            witness.insert(split.mask_cell, m.clone());
        }
        Ok((
            SplitState {
                pads,
                values,
                mask,
                id: self.id,
            },
            witness,
        ))
    }
    /// Run the frontend and reduce its constraints to the claim its storage
    /// discharges (`split_claim`), before the split challenge.
    pub fn prove_split<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        state: SplitState<W, F>,
        t: &mut TranscriptRef<'_>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(sumcheck::SumcheckProof<W, F>, PendingSplit<F::E>), String> {

        self.split()?;
        self.validate_circuits(circuit, public.len(), &[])?;
        if state.id != self.id {
            return Err("split state belongs to another circuit".into());
        }
        let f = ctx.field();
        let public = self.backend.parameters.extension().input_elements(f, public);
        let mut inputs = public.to_vec();
        inputs.extend_from_slice(&state.values[..self.inputs.committed()]);
        t.write_sumcheck_statement(circuit, &public, f);
        let (proof, constraints) = sumcheck::evaluate_and_prove_circuits(
            &[circuit],
            inputs,
            &state.pads,
            t,
            f,
        )?;
        let claim = self.split_claim(circuit, &public, constraints, t, f)?;
        Ok((
            proof,
            PendingSplit {
                claim,
                values: state.values,
                mask: state.mask,
            },
        ))
    }
}
