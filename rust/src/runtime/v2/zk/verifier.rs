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
                polygero::{validate_opening, PolygeroConfig},
                sumcheck::SumcheckProof,
                zk::{CircuitProof, ZkProof, ZkProofGeometry},
            },
            sumcheck::{self, TopWeights},
            transcript::{
                Bound, Challenge, Opened, Transcript, Unverified, VerifiedProof, ZkStatement,
            },
            zk::{
                joint::{top_weights, CircuitParticipant, FrontendPart, JointParam},
                packing_commitment::PackingCommitment,
                split::SplitClaim,
                CircuitInput, VirtualInputs, ZkContext, ZkProofStatement,
            },
        },
    },
};
/// Reduce the circuits of `t`'s frontend part on its public inputs to affine
/// equations awaiting authentication. This returns constraints, not an
/// acceptance decision: the caller must verify their joint Polygero proof
/// against the root received before sumcheck.
///
/// `top` is the frontend's top weights, drawn by the caller
/// (`joint::top_weights`). `virtual_inputs` must be the definitions the
/// prover used. They must be fixed before the caller draws `top`: derive
/// them only from data the transcript already binds, never from this proof's
/// own messages.
pub fn reduce<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    proof: &CircuitProof<W, F>,
    top: Challenge<TopWeights<F::E>>,
    virtual_inputs: &VirtualInputs<F::E>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<LinearStatement<F::E>, String> {
    reduce_parts(
        t,
        &proof.sumcheck_proof,
        &proof.packing,
        top,
        virtual_inputs,
        ctx,
    )
}
fn reduce_parts<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    sumcheck: &SumcheckProof<W, F>,
    packing: &PackingProof<F::E>,
    top: Challenge<TopWeights<F::E>>,
    virtual_inputs: &VirtualInputs<F::E>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<LinearStatement<F::E>, String> {
    let part = t.part();
    let p = part.participant;
    virtual_inputs.validate(&p.inputs)?;
    sumcheck
        .validate(&p.geometry.sc_geom)
        .map_err(|e| e.to_string())?;
    let f = ctx.field();
    let constraints = sumcheck::derive_constraints_for_circuits(
        &part.circuits,
        sumcheck,
        top,
        &mut t.transcript(),
        f,
    )?;
    let pads = p.geometry.sc_geom.pad_layout(p.backend.layout.suffix_start);
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
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkVerifier<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        let participant = CircuitParticipant::new(&[&circuit], 0, config, ctx)
            .map_err(ZkVerificationError::PolygeroVerification)?;
        Ok(Self {
            circuit,
            participant,
        })
    }
    /// The geometry the statement writes and the proof is parsed against.
    /// Its profile is the participant's, the one verification uses.
    pub fn geometry(&self) -> ZkProofGeometry {
        let circuit = self.participant.geometry();
        ZkProofGeometry {
            config: circuit.com_geom.config(),
            circuit,
        }
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
        Ok(ZkProofStatement {
            identity: ZkStatement { context },
            part: FrontendPart::new(&self.participant, &[&self.circuit], public)
                .map_err(ZkVerificationError::InvalidSumcheck)?,
            geometry: self.geometry(),
        })
    }
    /// Verify `proof` against the statement `session` opened with.
    pub fn verify<D: EvaluationDomain<W, F>>(
        &self,
        session: Opened<'_, ZkProofStatement<'_, W, F>>,
        proof: Unverified<'_, ZkProof<W, F>>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<VerifiedProof, ZkVerificationError> {
        let transcript = self.reduce(session, &proof, ctx)?;
        proof
            .checked(transcript)
            .map_err(|e| ZkVerificationError::InvalidTranscriptSeal(e.into()))
    }
    pub(crate) fn reduce<D: EvaluationDomain<W, F>>(
        &self,
        session: Opened<'_, ZkProofStatement<'_, W, F>>,
        proof: &ZkProof<W, F>,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Transcript, ZkVerificationError> {
        let (statement, t) = session.into_parts();
        if !std::ptr::eq(statement.part.participant, &self.participant) {
            return Err(ZkVerificationError::InvalidSumcheck(
                "statement belongs to another verifier".into(),
            ));
        }
        proof
            .sumcheck_proof
            .validate(&self.participant.geometry.sc_geom)
            .map_err(|e| ZkVerificationError::InvalidSumcheck(e.to_string()))?;
        // Reject malformed opening shapes before replaying the circuit transcript.
        // The joint backend also validates them for callers that use it directly.
        proof
            .com_proof
            .bodies
            .0
            .validate(&self.participant.geometry.com_geom)
            .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))?;
        validate_opening(
            &proof.com_proof.opening,
            self.participant.geometry.com_geom.t,
            self.participant.geometry.com_geom.n,
        )
        .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))?;
        let param = JointParam::new((
            self.participant
                .participant(ctx)
                .map_err(ZkVerificationError::PolygeroVerification)?,
            (),
        ))
        .map_err(ZkVerificationError::PolygeroVerification)?;
        let mut verifier = param.receive(&proof.com, (proof.fingerprints.clone(), ()), t);
        let mut frontend = verifier.bound(&statement.part);
        let linear = top_weights(&mut frontend)
            .and_then(|top| {
                reduce_parts(
                    &mut frontend,
                    &proof.sumcheck_proof,
                    &proof.packing,
                    top,
                    &VirtualInputs::none(),
                    ctx,
                )
            })
            .map_err(ZkVerificationError::InvalidSumcheck)?;
        let statements = (linear, ());
        let batch = verifier.weights(&statements);
        verifier
            .authenticate(batch, &proof.com_proof, statements)
            .map(|authenticated| authenticated.into_transcript())
            .map_err(ZkVerificationError::PolygeroVerification)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    InvalidSumcheck(String),
    InvalidTranscriptSeal(String),
    PublicInputLengthMismatch { expected: usize, actual: usize },
    PolygeroVerification(String),
}

impl fmt::Display for ZkVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSumcheck(message) => write!(f, "Invalid sumcheck: {message}"),
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

/// Check the split frontend proof of `t`'s part from its top weights `top`
/// and reduce its constraints to the claim its storage discharges
/// (`split_claim`), before the split challenge.
pub fn reduce_split<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    proof: &SumcheckProof<W, F>,
    top: Challenge<TopWeights<F::E>>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<SplitClaim<F::E>, String> {
    let part = t.part();
    let p = part.participant;
    p.split()?;
    proof
        .validate(&p.geometry.sc_geom)
        .map_err(|e| e.to_string())?;
    let f = ctx.field();
    let constraints = sumcheck::derive_constraints_for_circuits(
        &part.circuits,
        proof,
        top,
        &mut t.transcript(),
        f,
    )?;
    CircuitParticipant::split_claim(t, constraints, f)
}
