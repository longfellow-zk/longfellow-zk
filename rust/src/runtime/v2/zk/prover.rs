// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prepare circuit witnesses, reduce sumcheck and packing, then open Polygero.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        random::PrivateRandom,
        v2::{
            polygero::{FieldState, LinearStatement},
            proto::{
                polygero::{PolygeroCommitment, PolygeroConfig},
                sumcheck::SumcheckProof,
                witness_selection::{FingerprintResponse, FINGERPRINTS},
                zk::{CircuitGeometry, CircuitProof, ZkProof, ZkProofGeometry},
            },
            sumcheck::{self, SumcheckPads, TopWeights},
            transcript::{Bound, Challenge, Transcript, ZkStatement},
            zk::{
                context::private_input_count,
                joint::{top_weights, CircuitParticipant, FrontendPart, JointParam},
                packing_commitment::{prover::PackingState, PackingCommitment},
                split::PendingSplit,
                storage::{Split, Storage},
                CircuitInput, InputLayout, JointProver, VirtualInputs, ZkContext, ZkProofStatement,
            },
        },
    },
};

/// The participant a prover state was prepared by: its circuits, profile,
/// geometry, input layout and storage. Two participants over one context
/// have equal identities exactly when they are the same participant.
struct Identity {
    id: [u8; 32],
    additional_ids: Vec<[u8; 32]>,
    config: PolygeroConfig,
    geometry: CircuitGeometry,
    inputs: InputLayout,
    storage: Option<Split>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    fn identity(&self) -> Identity {
        Identity {
            id: self.id,
            additional_ids: self.additional_ids.clone(),
            config: self.config,
            geometry: self.geometry.clone(),
            inputs: self.inputs,
            storage: self.storage.clone(),
        }
    }
    /// Whether this participant prepared the state that recorded `identity`.
    fn prepared(&self, identity: &Identity) -> bool {
        let Identity {
            id,
            additional_ids,
            config,
            geometry,
            inputs,
            storage,
        } = identity;
        *id == self.id
            && *additional_ids == self.additional_ids
            && *config == self.config
            && *geometry == self.geometry
            && *inputs == self.inputs
            && *storage == self.storage
    }
}

/// Owned private inputs and masks for reduction after the shared commitment.
pub struct CircuitState<const W: usize, F: ZkField<W> + PackingField> {
    private: Vec<CircuitInput<F>>,
    pads: SumcheckPads<W, F>,
    packing: PackingState<F::E>,
    participant: Identity,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Own, validate and pack typed inputs before sampling any masks. The returned
    /// witness belongs in the corresponding position of the Polygero tuple.
    pub fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(CircuitState<W, F>, Vec<F::E>), String> {
        let inputs = self.backend.prepare_inputs(&private)?;
        let (pads, suffix) = sumcheck::sample_pads(
            self.geometry.sumcheck(),
            rng,
            self.backend.parameters.field(),
        );
        let (packing, witness) = self.backend.prepare(inputs, suffix, rng);
        Ok((
            CircuitState {
                private,
                pads,
                packing,
                participant: self.identity(),
            },
            witness,
        ))
    }
}
/// Prove the circuits of `t`'s frontend part as one layered sumcheck on its
/// public inputs, then reduce its input claim through packing. `top` is the
/// frontend's top weights, drawn by the caller (`joint::top_weights`).
///
/// `virtual_inputs` defines this proof's virtual input suffix. Its
/// definitions must be fixed before the caller draws `top`: derive
/// them only from data the transcript already binds, never from this
/// proof's own messages. Use `VirtualInputs::none()` when the participant
/// has no virtual inputs.
///
/// The resulting affine statement is authenticated only when the caller
/// completes the shared Polygero proof against the original commitment.
/// Continue the transcript used for that commitment. All participants must
/// finish this reduction before the joint backend samples its challenges.
pub fn prove<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    state: CircuitState<W, F>,
    top: Challenge<TopWeights<F::E>>,
    virtual_inputs: &VirtualInputs<F::E>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
    let part = t.part();
    let p = part.participant;
    virtual_inputs.validate(&p.inputs)?;
    if !p.prepared(&state.participant) {
        return Err("commitment belongs to another participant".into());
    }
    state
        .pads
        .validate(p.geometry.sumcheck())
        .map_err(|e| e.to_string())?;
    let f = ctx.field();
    let private = p
        .backend
        .parameters
        .extension()
        .into_input_elements(f, state.private);
    let mut inputs = prepare_inputs(&part.public, private, virtual_inputs.entries.len());
    for v in &virtual_inputs.entries {
        let value = f.addf(&v.constant, &f.mulf(&v.coefficient, &inputs[v.source]));
        inputs.push(value);
    }
    let (sumcheck_proof, constraints) = sumcheck::evaluate_and_prove_circuits(
        &part.circuits,
        inputs,
        state.pads,
        top,
        &mut t.transcript(),
        f,
    )?;
    let pad_layout = p
        .geometry
        .sumcheck()
        .pad_layout(p.backend.layout.suffix_start);
    let statement = super::constraint_compiler::compile_packed(
        constraints,
        &pad_layout,
        &part.public,
        &p.backend.layout,
        virtual_inputs,
        f,
    )?;
    let (packing, statement) = PackingCommitment::prove::<W>(
        &mut t.project(|q| &q.participant.backend),
        state.packing,
        statement,
    )?;
    Ok((
        CircuitProof {
            sumcheck_proof,
            packing,
        },
        statement,
    ))
}

/// A standalone prover of one circuit under one Polygero profile.
pub struct ZkProver<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) circuit: Circuit<F>,
    participant: CircuitParticipant<W, F>,
}
/// A commitment on a transcript opened with `statement`; the proof is completed
/// against that same statement.
pub struct ZkProverCommitment<'s, const W: usize, F: ZkField<W> + PackingField> {
    statement: &'s ZkProofStatement<'s, W, F>,
    state: CircuitState<W, F>,
    joint: JointProver<
        (FieldState<F::E>, ()),
        ([Vec<F::E>; FINGERPRINTS], ()),
        (FingerprintResponse<F::E>, ()),
    >,
    commitment: PolygeroCommitment,
    fingerprints: FingerprintResponse<F::E>,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkProver<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let participant = CircuitParticipant::new(&[&circuit], 0, config, ctx)?;
        Ok(Self {
            circuit,
            participant,
        })
    }
    /// The statement of a proof of this circuit on `public` under `context`.
    pub fn statement<'a>(
        &'a self,
        context: &'a [u8],
        public: &'a [CircuitInput<F>],
    ) -> Result<ZkProofStatement<'a, W, F>, String> {
        Ok(ZkProofStatement {
            identity: ZkStatement { context },
            part: FrontendPart::new(&self.participant, &[&self.circuit], public)?,
            geometry: ZkProofGeometry::new(
                self.participant.geometry(),
                self.participant.polygero()?.config(),
            )
            .map_err(|e| e.to_string())?,
        })
    }
    /// Open a transcript with `statement` and commit to `private`. The
    /// commitment remembers the statement, which `prove` completes.
    pub fn commit<'s, D: EvaluationDomain<W, F>, R: PrivateRandom>(
        &self,
        private: Vec<CircuitInput<F>>,
        statement: &'s ZkProofStatement<'s, W, F>,
        ctx: &ZkContext<'_, W, F, D>,
        rng: &mut R,
    ) -> Result<ZkProverCommitment<'s, W, F>, String> {
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let (state, witness) = self.participant.prepare(private, rng)?;
        let param = JointParam::new((self.participant.participant(ctx)?, ()))?;
        let (joint, commitment, (fingerprints, ())) =
            param.commit((witness, ()), Transcript::new(statement), rng)?;
        Ok(ZkProverCommitment {
            statement,
            state,
            joint,
            commitment,
            fingerprints,
        })
    }
    /// Complete the proof of the statement `committed` was opened with.
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        mut committed: ZkProverCommitment<'_, W, F>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(ZkProof<W, F>, Transcript), String> {
        let statement = committed.statement;
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        let mut t = committed.joint.bound(&statement.part);
        let top = top_weights(&mut t)?;
        let (circuit, linear) = prove(&mut t, committed.state, top, &VirtualInputs::none(), ctx)?;
        let param = JointParam::new((self.participant.participant(ctx)?, ()))?;
        // The opening follows the frontend's last message.
        let (com_proof, transcript) = committed.joint.finish(&param, (linear, ()))?;
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
/// Lays out the public and private inputs, reserving room for `nvirtual`
/// virtual inputs: sumcheck keeps this vector while it proves the layers,
/// so growing it afterwards would keep twice its capacity alive.
fn prepare_inputs<E: Clone>(public: &[E], private: Vec<E>, nvirtual: usize) -> Vec<E> {
    let mut inputs = Vec::with_capacity(public.len() + private.len() + nvirtual);
    inputs.extend_from_slice(public);
    inputs.extend(private);
    inputs
}
#[cfg(test)]
mod tests;

/// Prover state of a split participant between commitment and reduction.
pub struct SplitState<const W: usize, F: ZkField<W>> {
    pads: SumcheckPads<W, F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    mask: Option<F::E>,
    participant: Identity,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Sample pads and return the native witness `[native private inputs |
    /// pads | R]`, which is empty for pure foreign storage. `mask` is R, present
    /// exactly when some values are native.
    pub fn prepare_split(
        &self,
        private: Vec<CircuitInput<F>>,
        mask: Option<F::E>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(SplitState<W, F>, Vec<F::E>), String> {
        let split = self.split()?;
        if mask.is_some() != split.mask.is_some() || private.len() != self.inputs.committed() {
            return Err("split witness shape".into());
        }
        let f = self.backend.parameters.field();
        let mut values = self
            .backend
            .parameters
            .extension()
            .into_input_elements(f, private);
        let (pads, suffix) = sumcheck::sample_pads(self.geometry.sumcheck(), rng, f);
        values.extend(suffix);
        let mut witness: Vec<_> = split
            .map
            .entries()
            .iter()
            .zip(&values)
            .filter(|(s, _)| matches!(s, Storage::Native(_)))
            .map(|(_, v)| v.clone())
            .collect();
        // R follows every native value.
        witness.extend(mask.clone());
        Ok((
            SplitState {
                pads,
                values,
                mask,
                participant: self.identity(),
            },
            witness,
        ))
    }
}
/// Run the split frontend of `t`'s part from its top weights `top` and reduce
/// its constraints to the claim its storage discharges (`split_claim`),
/// before the split challenge.
pub fn prove_split<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    state: SplitState<W, F>,
    top: Challenge<TopWeights<F::E>>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<(SumcheckProof<W, F>, PendingSplit<F::E>), String> {
    let part = t.part();
    let p = part.participant;
    p.split()?;
    if !p.prepared(&state.participant) {
        return Err("split state belongs to another participant".into());
    }
    let f = ctx.field();
    let mut inputs = part.public.to_vec();
    inputs.extend_from_slice(&state.values[..p.inputs.committed()]);
    let (proof, constraints) = sumcheck::evaluate_and_prove_circuits(
        &part.circuits,
        inputs,
        state.pads,
        top,
        &mut t.transcript(),
        f,
    )?;
    let claim = CircuitParticipant::split_claim(t, constraints, f)?;
    Ok((
        proof,
        PendingSplit {
            claim,
            values: state.values,
            mask: state.mask,
        },
    ))
}
