// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Reconstruct each circuit's affine statement before the shared opening check.
use core::fmt;

use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        proto::Digest,
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            sumcheck::{self, TranscriptSumcheck},
            transcript::Transcript,
            zk::{
                joint::{CircuitParticipant, CircuitProof, JointParam},
                CircuitInput, ZkContext, ZkProof, ZkProofGeometry,
            },
        },
    },
};
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Returns constraints, not an acceptance decision: the caller must verify
    /// their joint Polygero proof against the root received before sumcheck.
    pub fn verify<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        proof: &CircuitProof<W, F>,
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<LinearStatement<F::E>, String> {
        self.verify_parts(
            circuit,
            public,
            &proof.sumcheck_proof,
            &proof.packing,
            &[],
            t,
            ctx,
        )
    }
    fn verify_parts<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        sumcheck: &crate::runtime::v2::proto::sumcheck::SumcheckProof<W, F>,
        packing: &crate::runtime::v2::proto::dual_packing::PackingProof<F::E>,
        others: &[&Circuit<F>],
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<LinearStatement<F::E>, String> {
        self.validate_circuits(circuit, public.len(), others)?;
        sumcheck
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        let public = self
            .backend
            .parameters
            .extension()
            .input_elements(ctx.f, public);
        let mut circuits = vec![circuit];
        circuits.extend_from_slice(others);
        for c in &circuits {
            t.write_sumcheck_statement(c, &public, ctx.f);
        }
        let constraints = sumcheck::derive_constraints_for_circuits(&circuits, sumcheck, t, ctx.f)?;
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile_packed::<W, F>(
            constraints,
            &pads,
            &public,
            &self.backend.layout,
            ctx.f,
        )?;
        self.backend.verify::<W>(statement, packing, &self.id, t)
    }
    /// Reduce all circuit statements to authenticated affine equations. The
    /// caller must still complete the shared Polygero verification.
    pub fn verify_circuits<D: EvaluationDomain<W, F>>(
        &self,
        circuit: &Circuit<F>,
        public: &[CircuitInput<F>],
        proof: &CircuitProof<W, F>,
        others: &[&Circuit<F>],
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<LinearStatement<F::E>, String> {
        self.verify_parts(
            circuit,
            public,
            &proof.sumcheck_proof,
            &proof.packing,
            others,
            t,
            ctx,
        )
    }
}
pub struct ZkVerifier<const W: usize, F: ZkField<W> + PackingField> {
    circuit: Circuit<F>,
    participant: CircuitParticipant<W, F>,
    joint_context: Digest,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkVerifier<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        let participant = CircuitParticipant::new(&circuit, config, ctx)
            .map_err(ZkVerificationError::PolygeroVerification)?;
        let param = JointParam::new((
            participant
                .participant(ctx)
                .map_err(ZkVerificationError::PolygeroVerification)?,
            (),
        ))
        .map_err(ZkVerificationError::PolygeroVerification)?;
        Ok(Self {
            circuit,
            participant,
            joint_context: param.context(),
        })
    }
    pub fn geometry(&self) -> ZkProofGeometry {
        ZkProofGeometry {
            circuit: self.participant.geometry(),
            joint_context: self.joint_context,
        }
    }
    pub(crate) fn public_input_count(&self) -> usize {
        self.circuit.raw.npublic_input
    }
    pub fn verify<D: EvaluationDomain<W, F>>(
        &self,
        public: &[CircuitInput<F>],
        proof: crate::runtime::v2::transcript::Unverified<'_, ZkProof<W, F>>,
        mut transcript: Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<crate::runtime::v2::transcript::VerifiedProof, ZkVerificationError> {
        self.reduce(public, &proof, &mut transcript, ctx)?;
        proof
            .checked(transcript)
            .map_err(|e| ZkVerificationError::InvalidSumcheck(e.into()))
    }
    pub(crate) fn reduce<D: EvaluationDomain<W, F>>(
        &self,
        public: &[CircuitInput<F>],
        proof: &ZkProof<W, F>,
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(), ZkVerificationError> {
        if public.len() != self.public_input_count() {
            return Err(ZkVerificationError::PublicInputLengthMismatch {
                expected: self.public_input_count(),
                actual: public.len(),
            });
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
        crate::runtime::v2::proto::polygero::validate_opening(
            &proof.com_proof.opening,
            self.participant.geometry.com_geom.t,
            self.participant.geometry.com_geom.n,
        )
        .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))?;
        self.participant.bind(t);
        let param = JointParam::new((
            self.participant
                .participant(ctx)
                .map_err(ZkVerificationError::PolygeroVerification)?,
            (),
        ))
        .map_err(ZkVerificationError::PolygeroVerification)?;
        let verifier = param
            .receive(&proof.com, (proof.fingerprints.clone(), ()), t)
            .map_err(ZkVerificationError::PolygeroVerification)?;
        let statement = self
            .participant
            .verify_parts(
                &self.circuit,
                public,
                &proof.sumcheck_proof,
                &proof.packing,
                &[],
                t,
                ctx,
            )
            .map_err(ZkVerificationError::InvalidSumcheck)?;
        verifier
            .authenticate(&proof.com_proof, (statement, ()), t)
            .map(|_| ())
            .map_err(ZkVerificationError::PolygeroVerification)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    InvalidSumcheck(String),
    PublicInputLengthMismatch { expected: usize, actual: usize },
    PolygeroVerification(String),
}

impl fmt::Display for ZkVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSumcheck(message) => write!(f, "Invalid sumcheck: {message}"),
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
