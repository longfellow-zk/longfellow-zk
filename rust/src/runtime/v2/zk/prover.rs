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
                zk::{CircuitProof, CircuitProofGeometry, ZkProof},
            },
            sumcheck::{self, symbolic::Constraints, SumcheckPads},
            transcript::{Bound, EncodedProof, Transcript},
            zk::{
                context::private_input_count,
                joint::{CircuitParticipant, Frontend, FrontendPart, JointParam, Participant},
                packing_commitment::{prover::PackingState, PackingCommitment},
                split::{MixedSplit, PendingSplit},
                storage::{MixedStorage, Storage},
                CircuitInput, InputLayout, JointProver, VirtualInputs, ZkProofStatement,
            },
        },
    },
};

/// The participant a prover state was prepared by: its circuits, profile,
/// geometry, input layout and storage `S` (`()` for native storage).
/// Identities compare these values, not the participant objects: two
/// participants that agree on all of them have equal identities and may
/// finish each other's states.
pub(super) struct Identity<S> {
    id: [u8; 32],
    additional_ids: Vec<[u8; 32]>,
    config: PolygeroConfig,
    geometry: CircuitProofGeometry,
    inputs: InputLayout,
    storage: S,
}
impl<const W: usize, F: ZkField<W> + PackingField> Frontend<W, F> {
    pub(super) fn identity<S>(&self, storage: S) -> Identity<S> {
        Identity {
            id: self.id,
            additional_ids: self.additional_ids.clone(),
            config: self.config,
            geometry: self.geometry.clone(),
            inputs: self.inputs,
            storage,
        }
    }
    /// Whether this frontend, with `storage`, matches the participant that
    /// prepared the state that recorded `identity`.
    pub(super) fn prepared<S: PartialEq>(&self, identity: &Identity<S>, storage: &S) -> bool {
        let Identity {
            id,
            additional_ids,
            config,
            geometry,
            inputs,
            storage: prepared,
        } = identity;
        *id == self.id
            && *additional_ids == self.additional_ids
            && *config == self.config
            && *geometry == self.geometry
            && *inputs == self.inputs
            && prepared == storage
    }
}

/// Owned private inputs and masks for reduction after the shared commitment.
pub(crate) struct CircuitState<const W: usize, F: ZkField<W> + PackingField> {
    private: Vec<CircuitInput<F>>,
    pads: SumcheckPads<W, F>,
    packing: PackingState<F::E>,
    participant: Identity<()>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Own, validate and pack typed inputs before sampling any masks. The returned
    /// witness belongs in the corresponding position of the Polygero tuple.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(CircuitState<W, F>, Vec<F::E>), String> {
        let p = &self.frontend;
        let inputs = p.backend.prepare_inputs(&private)?;
        let (pads, suffix) = sumcheck::sample_pads(p.geometry.sumcheck(), rng, p.field());
        let (packing, witness) = p.backend.prepare(inputs, suffix, rng);
        Ok((
            CircuitState {
                private,
                pads,
                packing,
                participant: p.identity(()),
            },
            witness,
        ))
    }
}
/// Prove the circuits of `t`'s frontend part as one layered sumcheck on its
/// public inputs, then reduce its input claim through packing. The sumcheck
/// draws the frontend's top weights on entry, before its first message.
///
/// `virtual_inputs` defines this proof's virtual input suffix. As an
/// argument of the call that draws the top weights, it is fixed before
/// them; derive it only from data the transcript already binds, never from
/// this proof's own messages. Use `VirtualInputs::none()` when the participant
/// has no virtual inputs.
///
/// The resulting affine statement is authenticated only when the caller
/// completes the shared Polygero proof against the original commitment.
/// Continue the transcript used for that commitment. All participants must
/// finish this reduction before the joint backend samples its challenges.
pub(crate) fn prove<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    state: CircuitState<W, F>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<(CircuitProof<W, F>, LinearStatement<F::E>), String> {
    let part = t.part();
    let p = part.frontend();
    virtual_inputs.validate(&p.inputs)?;
    if !p.prepared(&state.participant, &()) {
        return Err("commitment belongs to another participant".into());
    }
    state
        .pads
        .validate(p.geometry.sumcheck())
        .map_err(|e| e.to_string())?;
    let f = part.field();
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
        part.circuits(),
        inputs,
        state.pads,
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
        &mut t.project(|q| &q.participant.frontend.backend),
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
        domain: &D,
    ) -> Result<Self, String> {
        let participant = CircuitParticipant::new(&[&circuit], 0, config, domain)?;
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
        ZkProofStatement::new(context, &self.participant, &self.circuit, public)
    }
    /// Open a transcript with `statement` and commit to `private`. The
    /// commitment remembers the statement, which `prove` completes.
    pub fn commit<'s, D: EvaluationDomain<W, F>, R: PrivateRandom>(
        &self,
        private: Vec<CircuitInput<F>>,
        statement: &'s ZkProofStatement<'s, W, F>,
        domain: &D,
        rng: &mut R,
    ) -> Result<ZkProverCommitment<'s, W, F>, String> {
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let (state, witness) = self.participant.prepare(private, rng)?;
        let param = JointParam::new((self.participant.participant(domain)?, ()))?;
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
    /// Complete the proof of the statement `committed` was opened with and
    /// seal it against the geometry that statement wrote (transcript I10).
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        mut committed: ZkProverCommitment<'_, W, F>,
        domain: &D,
    ) -> Result<EncodedProof, String> {
        let statement = committed.statement;
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        let mut t = committed.joint.bound(&statement.part);
        let (circuit, linear) = prove(&mut t, committed.state, &VirtualInputs::none())?;
        let param = JointParam::new((self.participant.participant(domain)?, ()))?;
        // The opening follows the frontend's last message.
        let (com_proof, transcript) = committed.joint.finish(&param, (linear, ()))?;
        let proof = ZkProof {
            com: committed.commitment,
            fingerprints: committed.fingerprints,
            sumcheck_proof: circuit.sumcheck_proof,
            packing: circuit.packing,
            com_proof,
        };
        proof
            .write(&statement.geometry, self.participant.field(), transcript)
            .map_err(|e| e.to_string())
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

/// Prover state of a mixed split participant between commitment and
/// reduction.
pub(crate) struct SplitState<const W: usize, F: ZkField<W>> {
    pads: SumcheckPads<W, F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    /// The split mask R.
    mask: F::E,
    participant: Identity<MixedStorage>,
}
impl<const W: usize, F: ZkField<W> + PackingField> MixedSplit<W, F> {
    /// Sample pads and return the native witness `[native private inputs |
    /// pads | R]`; `mask` is R.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        mask: F::E,
        rng: &mut impl PrivateRandom,
    ) -> Result<(SplitState<W, F>, Vec<F::E>), String> {
        let p = &self.frontend;
        if private.len() != p.inputs.committed() {
            return Err("split witness shape".into());
        }
        let f = p.field();
        let mut values = p
            .backend
            .parameters
            .extension()
            .into_input_elements(f, private);
        let (pads, suffix) = sumcheck::sample_pads(p.geometry.sumcheck(), rng, f);
        values.extend(suffix);
        let mut witness: Vec<_> = self
            .storage
            .map
            .entries()
            .iter()
            .zip(&values)
            .filter(|(s, _)| matches!(s, Storage::Native(_)))
            .map(|(_, v)| v.clone())
            .collect();
        // R follows every native value.
        witness.push(mask.clone());
        Ok((
            SplitState {
                pads,
                values,
                mask,
                participant: p.identity(self.storage.clone()),
            },
            witness,
        ))
    }
}
/// Run the sumcheck of a split frontend of `t`'s part over `[public |
/// private inputs]`, the private inputs leading `values`; it draws its top
/// weights on entry. Every split storage mode runs its frontend here.
pub(super) fn prove_values<const W: usize, F: ZkField<W> + PackingField, P: Participant<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F, P>>,
    values: &[F::E],
    pads: SumcheckPads<W, F>,
) -> Result<(SumcheckProof<W, F>, Constraints<F::E>), String> {
    let part = t.part();
    let mut inputs = part.public.to_vec();
    inputs.extend_from_slice(&values[..part.frontend().inputs.committed()]);
    sumcheck::evaluate_and_prove_circuits(
        part.circuits(),
        inputs,
        pads,
        &mut t.transcript(),
        part.field(),
    )
}
/// Run the mixed split frontend of `t`'s part and reduce its constraints to
/// the claim its storage discharges (`split_claim`), before the split
/// challenge.
pub(crate) fn prove_split<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F, MixedSplit<W, F>>>,
    state: SplitState<W, F>,
) -> Result<(SumcheckProof<W, F>, PendingSplit<F::E>), String> {
    let p = t.part().participant;
    if !p.frontend.prepared(&state.participant, &p.storage) {
        return Err("split state belongs to another participant".into());
    }
    let (proof, constraints) = prove_values(t, &state.values, state.pads)?;
    let claim = MixedSplit::split_claim(t, constraints)?;
    Ok((
        proof,
        PendingSplit {
            claim,
            values: state.values,
            mask: state.mask,
        },
    ))
}
