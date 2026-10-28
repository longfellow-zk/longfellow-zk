// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared v2 verifier: symbolic sumcheck, packing, then the original commitment.
use core::fmt;

use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::{EvaluationDomain, IdentityExtension, PackingExtension, PackingField, ZkField},
        polygero::PolygeroConfig,
        random::Transcript,
        sumcheck_v2::{self, TranscriptSumcheck},
        zk_v2::{
            commitment::CommitmentVerifier, context::prepare_layout, ZkContext, ZkProof,
            ZkProofGeometry,
        },
    },
};
pub struct ZkVerifier<
    const W: usize,
    F: ZkField<W>,
    X: PackingExtension<Ambient = F> = <F as PackingField>::Packing,
> {
    circuit: Circuit<F>,
    geometry: ZkProofGeometry,
    commitment: CommitmentVerifier<F, X>,
}
impl<const W: usize, F: ZkField<W>> ZkVerifier<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        Self::with_extension(circuit, config, ctx.f.packing_extension(), ctx)
    }
    pub fn new_full_field<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<ZkVerifier<W, F, IdentityExtension<F>>, ZkVerificationError> {
        ZkVerifier::with_extension(circuit, config, IdentityExtension::new(ctx.f.clone()), ctx)
    }
}
impl<const W: usize, F: ZkField<W>, X: PackingExtension<Ambient = F>> ZkVerifier<W, F, X> {
    pub fn with_extension<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        extension: X,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        let (geometry, param, backend) = prepare_layout(&circuit, config, extension, ctx)
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
        public: &[F::E],
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
        if self.commitment.backend.layout.degree > 1 && public.first() != Some(&ctx.f.one()) {
            return Err(ZkVerificationError::InvalidSumcheck(
                "reserved One must equal one".into(),
            ));
        }
        proof
            .sumcheck_proof
            .validate(&self.geometry.sc_geom)
            .map_err(|e| ZkVerificationError::InvalidSumcheck(e.to_string()))?;
        proof
            .com_proof
            .validate(&self.geometry.com_geom)
            .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))?;
        t.write_sumcheck_statement(&self.circuit, public, ctx.f);
        let constraints =
            sumcheck_v2::derive_constraints(&self.circuit, &proof.sumcheck_proof, t, ctx.f)
                .map_err(ZkVerificationError::InvalidSumcheck)?;
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.commitment.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile::<W, F>(
            constraints,
            &pads,
            public,
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
            Self::InvalidSumcheck(s) => write!(f, "Invalid sumcheck: {s}"),
            Self::PublicInputLengthMismatch { expected, actual } => write!(
                f,
                "Public input length mismatch: expected {expected}, got {actual}"
            ),
            Self::PolygeroVerification(s) => write!(f, "Polygero commitment proof error: {s}"),
        }
    }
}
impl std::error::Error for ZkVerificationError {}
