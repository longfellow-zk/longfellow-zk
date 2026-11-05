// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared v2 verifier: symbolic sumcheck, packing, then the original commitment.
use core::fmt;

use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        polygero::PolygeroConfig,
        random::Transcript,
        sumcheck_v2::{self, TranscriptSumcheck},
        zk_v2::{
            commitment::CommitmentVerifier, context::prepare_layout, CircuitInput, ZkContext,
            ZkProof, ZkProofGeometry,
        },
    },
};
pub struct ZkVerifier<const W: usize, F: ZkField<W> + PackingField> {
    circuit: Circuit<F>,
    geometry: ZkProofGeometry,
    commitment: CommitmentVerifier<F, <F as PackingField>::Packing>,
}
impl<const W: usize, F: ZkField<W> + PackingField> ZkVerifier<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        let (geometry, param, backend) =
            prepare_layout(&circuit, config, ctx.f.packing_extension(), ctx)
                .map_err(ZkVerificationError::PolygeroVerification)?;
        Ok(Self {
            circuit,
            geometry,
            commitment: CommitmentVerifier::new(backend, param),
        })
    }
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }
    pub(crate) fn public_input_count(&self) -> usize {
        self.circuit.raw.npublic_input
    }
    pub fn receive_commitment(&mut self, proof: &ZkProof<W, F>, t: &mut Transcript) {
        self.commitment.receive(&proof.com, &self.circuit.id, t);
    }
    pub fn verify<D: EvaluationDomain<W, F>>(
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
            .validate(&self.geometry.sc_geom)
            .map_err(|e| ZkVerificationError::InvalidSumcheck(e.to_string()))?;
        proof
            .com_proof
            .validate(&self.geometry.com_geom)
            .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))?;
        let public = self
            .commitment
            .backend
            .parameters
            .extension()
            .input_elements(ctx.f, public);
        t.write_sumcheck_statement(&self.circuit, &public, ctx.f);
        let constraints =
            sumcheck_v2::derive_constraints(&self.circuit, &proof.sumcheck_proof, t, ctx.f)
                .map_err(ZkVerificationError::InvalidSumcheck)?;
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.commitment.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile_packed::<W, F>(
            constraints,
            &pads,
            &public,
            &self.commitment.backend.layout,
            ctx.f,
        )
        .map_err(ZkVerificationError::InvalidSumcheck)?;
        self.commitment
            .verify::<W, D>(
                statement,
                (&proof.packing, &proof.com, &proof.com_proof),
                &self.circuit.id,
                t,
                ctx.domain,
            )
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
