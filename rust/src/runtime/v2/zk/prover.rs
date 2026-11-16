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
            polygero::LinearStatement,
            proto::{
                polygero::{PolygeroCommitment, PolygeroConfig},
                sumcheck::SumcheckProof,
                witness_selection::FingerprintResponse,
                zk::{CircuitProof, ZkProof},
            },
            sumcheck::{self, symbolic::Constraints, SumcheckPads},
            transcript::{Bound, EncodedProof, Transcript},
            witness_selection::Field,
            zk::{
                context::private_input_count,
                joint::{CircuitParticipant, Frontend, FrontendPart, JointParam, Participant},
                packing_commitment::{prover::PackingState, PackingCommitment},
                split::{MixedSplit, PendingSplit},
                storage::{MixedStorage, Storage},
                CircuitInput, JointProver, VirtualInputs, ZkProofStatement,
            },
        },
    },
};

/// The participant a prover state was prepared by, borrowed from it: its
/// frontend, which holds its circuits, profile, geometry and input layout,
/// and its storage `S` (`()` for native storage). Identities compare these
/// values, not the participant objects: two participants that agree on all
/// of them have equal identities and may finish each other's states.
pub(super) struct Identity<'p, F: ZkField + PackingField, S> {
    frontend: &'p Frontend<F>,
    storage: &'p S,
}
impl<F: ZkField + PackingField> Frontend<F> {
    pub(super) fn identity<'p, S>(&'p self, storage: &'p S) -> Identity<'p, F, S> {
        Identity {
            frontend: self,
            storage,
        }
    }
    /// Whether this frontend, with `storage`, matches the participant that
    /// prepared the state that recorded `identity`.
    pub(super) fn prepared<S: PartialEq>(
        &self,
        identity: &Identity<'_, F, S>,
        storage: &S,
    ) -> bool {
        let Identity {
            frontend: prepared,
            storage: prepared_storage,
        } = identity;
        prepared.id == self.id
            && prepared.additional_ids == self.additional_ids
            && prepared.config == self.config
            && prepared.geometry == self.geometry
            && prepared.inputs == self.inputs
            && *prepared_storage == storage
    }
}

/// Owned private inputs and masks for reduction after the shared commitment,
/// with the identity of the participant `'p` that prepared them.
pub(crate) struct CircuitState<'p, F: ZkField + PackingField> {
    private: Vec<CircuitInput<F>>,
    pads: SumcheckPads<F>,
    packing: PackingState<F::E>,
    participant: Identity<'p, F, ()>,
}
impl<F: ZkField + PackingField> CircuitParticipant<F> {
    /// Own, validate and pack typed inputs before sampling any masks. The returned
    /// witness belongs in the corresponding position of the Polygero tuple.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(CircuitState<'_, F>, Vec<F::E>), String> {
        let p = &self.frontend;
        let inputs = p.backend.prepare_inputs(&private)?;
        let (pads, suffix) = sumcheck::sample_pads(p.geometry.sumcheck(), rng, p.field());
        let (packing, witness) = p.backend.prepare(inputs, suffix, rng);
        Ok((
            CircuitState {
                private,
                pads,
                packing,
                participant: p.identity(&()),
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
pub(crate) fn prove<F: ZkField + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, F>>,
    state: CircuitState<'_, F>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<(CircuitProof<F>, LinearStatement<F::E>), String> {
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
    let (packing, statement) = PackingCommitment::prove(
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
pub struct ZkProver<F: ZkField + PackingField> {
    pub(super) circuit: Circuit<F>,
    participant: CircuitParticipant<F>,
}
/// A commitment on a transcript opened with `statement`, over the domain
/// `D`; the proof is completed against that same statement, with the joint
/// parameter that committed.
pub struct ZkProverCommitment<'s, F: ZkField + PackingField, D: EvaluationDomain<F>> {
    statement: &'s ZkProofStatement<'s, F>,
    state: CircuitState<'s, F>,
    joint: JointProver<(Field<'s, F, D>, ())>,
    commitment: PolygeroCommitment,
    fingerprints: FingerprintResponse<F::E>,
}
impl<F: ZkField + PackingField> ZkProver<F> {
    pub fn new<D: EvaluationDomain<F>>(
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
    ) -> Result<ZkProofStatement<'a, F>, String> {
        ZkProofStatement::new(context, &self.participant, &self.circuit, public)
    }
    /// Open a transcript with `statement` and commit to `private`. The
    /// commitment remembers the statement, which `prove` completes.
    pub fn commit<'s, D: EvaluationDomain<F>, R: PrivateRandom>(
        &self,
        private: Vec<CircuitInput<F>>,
        statement: &'s ZkProofStatement<'s, F>,
        domain: &'s D,
        rng: &mut R,
    ) -> Result<ZkProverCommitment<'s, F, D>, String> {
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        // The statement's participant, checked above to be this prover's.
        let participant = statement.part.participant;
        let (state, witness) = participant.prepare(private, rng)?;
        let param = JointParam::new((participant.participant(domain)?, ()))?;
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
    pub fn prove<D: EvaluationDomain<F>>(
        &self,
        mut committed: ZkProverCommitment<'_, F, D>,
    ) -> Result<EncodedProof, String> {
        let statement = committed.statement;
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err("statement belongs to another prover".into());
        }
        let mut t = committed.joint.bound(&statement.part);
        let (circuit, linear) = prove(&mut t, committed.state, &VirtualInputs::none())?;
        // The opening follows the frontend's last message.
        let (com_proof, transcript) = committed.joint.finish((linear, ()))?;
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

/// Prover state of a mixed split participant `'p` between commitment and
/// reduction.
pub(crate) struct SplitState<'p, F: ZkField + PackingField> {
    pads: SumcheckPads<F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    /// The split mask R.
    mask: F::E,
    participant: Identity<'p, F, MixedStorage>,
}
impl<F: ZkField + PackingField> MixedSplit<F> {
    /// Sample pads and return the native witness `[native private inputs |
    /// pads | R]`; `mask` is R.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        mask: F::E,
        rng: &mut impl PrivateRandom,
    ) -> Result<(SplitState<'_, F>, Vec<F::E>), String> {
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
                participant: p.identity(&self.storage),
            },
            witness,
        ))
    }
}
/// Run the sumcheck of a split frontend of `t`'s part over `[public |
/// private inputs]`, the private inputs leading `values`; it draws its top
/// weights on entry. Every split storage mode runs its frontend here.
pub(super) fn prove_values<F: ZkField + PackingField, P: Participant<F>>(
    t: &mut Bound<'_, FrontendPart<'_, F, P>>,
    values: &[F::E],
    pads: SumcheckPads<F>,
) -> Result<(SumcheckProof<F>, Constraints<F::E>), String> {
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
pub(crate) fn prove_split<F: ZkField + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>,
    state: SplitState<'_, F>,
) -> Result<(SumcheckProof<F>, PendingSplit<F::E>), String> {
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
