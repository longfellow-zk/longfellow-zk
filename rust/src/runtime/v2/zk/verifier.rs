// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Reconstruct each circuit's affine statement before the shared opening check.
use core::fmt;

use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{packing::PackingField, range_interpolation::EvaluationDomain, ZkField},
        v2::{
            polygero::LinearStatement,
            proto::{
                dual_packing::PackingProof,
                polygero::PolygeroConfig,
                sumcheck::SumcheckProof,
                zk::{CircuitProof, ZkProof, ZkProofGeometry},
            },
            sumcheck::{self, symbolic::Constraints},
            transcript::{Bound, Opened, Unverified, VerifiedProof},
            zk::{
                joint::{CircuitParticipant, FrontendPart, JointParam},
                packing_commitment::PackingCommitment,
                split::SplitClaim,
                Authenticated, CircuitInput, VirtualInputs, ZkProofStatement,
            },
        },
    },
};
/// Reduce the circuits of `t`'s frontend part on its public inputs to affine
/// equations awaiting authentication. This returns constraints, not an
/// acceptance decision: the caller must verify their joint Polygero proof
/// against the root received before sumcheck.
///
/// The sumcheck draws the frontend's top weights on entry. `virtual_inputs`
/// must be the definitions the prover used. As an argument of the call that
/// draws the top weights, they are fixed before them; derive them only from
/// data the transcript already binds, never from this proof's own messages.
pub(crate) fn reduce<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    proof: &CircuitProof<W, F>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<LinearStatement<F::E>, String> {
    reduce_parts(t, &proof.sumcheck_proof, &proof.packing, virtual_inputs)
}
fn reduce_parts<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    sumcheck: &SumcheckProof<W, F>,
    packing: &PackingProof<F::E>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<LinearStatement<F::E>, String> {
    let constraints = sumcheck_constraints(t, sumcheck, virtual_inputs)?;
    pack_constraints(t, constraints, packing, virtual_inputs)
}
/// The sumcheck step: check the frontend's sumcheck proof, drawing its top
/// weights, and derive its constraints on the committed cells.
fn sumcheck_constraints<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    sumcheck: &SumcheckProof<W, F>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<Constraints<F::E>, String> {
    let part = t.part();
    let p = part.participant;
    virtual_inputs.validate(&p.inputs)?;
    sumcheck
        .validate(p.geometry.sumcheck())
        .map_err(|e| e.to_string())?;
    sumcheck::derive_constraints_for_circuits(
        part.circuits(),
        sumcheck,
        &mut t.transcript(),
        part.field(),
    )
}
/// The packing step: compile the constraints onto the packed commitment and
/// reduce them, with the packing proof, to equations on the committed row.
fn pack_constraints<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    constraints: Constraints<F::E>,
    packing: &PackingProof<F::E>,
    virtual_inputs: &VirtualInputs<F::E>,
) -> Result<LinearStatement<F::E>, String> {
    let part = t.part();
    let p = part.participant;
    let f = part.field();
    let pads = p
        .geometry
        .sumcheck()
        .pad_layout(p.backend.layout.suffix_start);
    let statement = super::constraint_compiler::compile_packed::<W, F>(
        constraints,
        &pads,
        &part.public,
        &p.backend.layout,
        virtual_inputs,
        f,
    )?;
    PackingCommitment::reduce::<W>(
        &mut t.project(|q| &q.participant.backend),
        statement,
        packing,
    )
}
/// A standalone verifier of one circuit under one Polygero profile.
pub struct ZkVerifier<const W: usize, F: ZkField<W> + PackingField> {
    circuit: Circuit<F>,
    participant: CircuitParticipant<W, F>,
    geometry: ZkProofGeometry,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkVerifier<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, ZkVerificationError> {
        let participant = CircuitParticipant::new(&[&circuit], 0, config, domain)
            .map_err(ZkVerificationError::InvalidStatement)?;
        let profile = participant
            .polygero()
            .map_err(ZkVerificationError::InvalidStatement)?
            .config();
        let geometry = ZkProofGeometry::new(participant.geometry(), profile)
            .map_err(|e| ZkVerificationError::InvalidStatement(e.to_string()))?;
        Ok(Self {
            circuit,
            participant,
            geometry,
        })
    }
    /// The geometry the statement writes and the proof is parsed against.
    /// Its profile is the participant's, the one verification uses.
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }
    pub(crate) fn public_input_count(&self) -> usize {
        self.circuit.raw.npublic_input
    }
    /// The statement of a proof of this circuit on `public` under `context`.
    /// Open a session with it (`Opened::new`), parse the proof against its
    /// geometry (`ZkProof::read` with `Opened::geometry`), then verify on that
    /// session.
    pub fn statement<'a>(
        &'a self,
        context: &'a [u8],
        public: &'a [CircuitInput<F>],
    ) -> Result<ZkProofStatement<'a, W, F>, ZkVerificationError> {
        if public.len() != self.public_input_count() {
            return Err(ZkVerificationError::PublicInputLengthMismatch {
                expected: self.public_input_count(),
                actual: public.len(),
            });
        }
        ZkProofStatement::new(context, &self.participant, &self.circuit, public)
            .map_err(ZkVerificationError::InvalidStatement)
    }
    /// Verify `proof` against the statement `session` opened with.
    #[doc = include_str!("verifier_compile_fail.md")]
    pub fn verify<D: EvaluationDomain<W, F>>(
        &self,
        session: Opened<'_, ZkProofStatement<'_, W, F>>,
        proof: Unverified<'_, ZkProof<W, F>>,
        domain: &D,
    ) -> Result<VerifiedProof, ZkVerificationError> {
        self.reduce(session, &proof, domain)?
            .check_seal(proof)
            .map_err(|e| ZkVerificationError::InvalidTranscriptSeal(e.into()))
    }
    pub(crate) fn reduce<D: EvaluationDomain<W, F>>(
        &self,
        session: Opened<'_, ZkProofStatement<'_, W, F>>,
        proof: &ZkProof<W, F>,
        domain: &D,
    ) -> Result<Authenticated, ZkVerificationError> {
        let (statement, t) = session.into_parts();
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err(ZkVerificationError::InvalidStatement(
                "statement belongs to another verifier".into(),
            ));
        }
        // The reader parsed the proof against the statement's geometry, and
        // the joint backend checks the opening's shape before using it.
        let param = JointParam::new((
            self.participant
                .participant(domain)
                .map_err(ZkVerificationError::PolygeroVerification)?,
            (),
        ))
        .map_err(ZkVerificationError::PolygeroVerification)?;
        let mut verifier = param.receive(&proof.com, (proof.fingerprints.clone(), ()), t);
        let mut frontend = verifier.bound(&statement.part);
        let none = VirtualInputs::none();
        let constraints = sumcheck_constraints(&mut frontend, &proof.sumcheck_proof, &none)
            .map_err(ZkVerificationError::InvalidSumcheck)?;
        let linear = pack_constraints(&mut frontend, constraints, &proof.packing, &none)
            .map_err(ZkVerificationError::InvalidPacking)?;
        verifier
            .finish((linear, ()), &proof.com_proof)
            .map_err(ZkVerificationError::PolygeroVerification)
    }
}
/// Why the standalone verifier rejected, by the layer that failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    /// The circuit and profile do not form a verifier, its statement cannot
    /// be built, or the session was opened with another verifier's statement.
    InvalidStatement(String),
    /// The statement's public inputs do not match the circuit's count.
    PublicInputLengthMismatch { expected: usize, actual: usize },
    /// The sumcheck proof, from its top weights to the derived constraints.
    InvalidSumcheck(String),
    /// The constraint compiler or the dual-packing reduction.
    InvalidPacking(String),
    /// The joint commitment: its participant, fingerprints and opening.
    PolygeroVerification(String),
    /// The seal over the proof bytes.
    InvalidTranscriptSeal(String),
}

impl fmt::Display for ZkVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStatement(message) => write!(f, "Invalid statement: {message}"),
            Self::InvalidSumcheck(message) => write!(f, "Invalid sumcheck: {message}"),
            Self::InvalidPacking(message) => write!(f, "Invalid packing: {message}"),
            Self::InvalidTranscriptSeal(message) => write!(f, "Invalid transcript seal: {message}"),
            Self::PublicInputLengthMismatch { expected, actual } => {
                write!(
                    f,
                    "Public input length mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            Self::PolygeroVerification(err) => {
                write!(f, "Polygero commitment proof error: {}", err)
            }
        }
    }
}

impl std::error::Error for ZkVerificationError {}

/// Check the split frontend proof of `t`'s part, drawing its top weights,
/// and reduce its constraints to the claim its storage discharges
/// (`split_claim`), before the split challenge.
pub(crate) fn reduce_split<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    proof: &SumcheckProof<W, F>,
) -> Result<SplitClaim<F::E>, String> {
    let part = t.part();
    let p = part.participant;
    p.split()?;
    proof
        .validate(p.geometry.sumcheck())
        .map_err(|e| e.to_string())?;
    let f = part.field();
    let constraints =
        sumcheck::derive_constraints_for_circuits(part.circuits(), proof, &mut t.transcript(), f)?;
    CircuitParticipant::split_claim(t, constraints)
}
