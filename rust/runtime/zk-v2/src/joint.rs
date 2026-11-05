// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit metadata shared by standalone proofs and joint field commitments.
use super::{
    commitment::PackingCommitment, context::prepare_circuit_layout, ZkContext, ZkProofGeometry,
};
pub use crate::runtime::proto::zk_v2::CircuitProof;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingField, ZkField},
        polygero::{Participant, PolygeroConfig, PolygeroParam},
        random::Transcript,
    },
};

/// A circuit's packing and commitment layout, independent of the participant list.
/// The application binds each participant before committing the shared column tree.
/// Input packing stays here; the lower-level Polygero participant only knows
/// full-field witness cells and affine constraints over them.
pub struct CircuitParticipant<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) geometry: ZkProofGeometry,
    #[cfg(any(test, feature = "prover"))]
    pub(super) config: PolygeroConfig,
    pub(super) param: PolygeroParam,
    pub(super) backend: PackingCommitment<F>,
    pub(super) id: [u8; 32],
    pub(super) additional_ids: Vec<[u8; 32]>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        Self::with_circuits(circuit, &[], config, ctx)
    }
    /// Prove these circuits as one layered sumcheck. They share the same input
    /// counts and public/private ordering. Each intermediate layer has one wire
    /// array; only the sparse quad terms retain their circuit-local indexing.
    pub fn with_circuits<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        others: &[&Circuit<F>],
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let (geometry, param, backend) =
            prepare_circuit_layout(circuit, others, config, ctx.f.packing_extension(), ctx)?;
        Ok(Self {
            geometry,
            #[cfg(any(test, feature = "prover"))]
            config,
            param,
            backend,
            id: circuit.id,
            additional_ids: others.iter().map(|c| c.id).collect(),
        })
    }
    pub(super) fn validate_circuits(
        &self,
        circuit: &Circuit<F>,
        public: usize,
        others: &[&Circuit<F>],
    ) -> Result<(), String> {
        if circuit.id != self.id
            || public != circuit.raw.npublic_input
            || self.additional_ids.len() != others.len()
        {
            return Err("joint circuit statement mismatch".into());
        }
        for (id, c) in self.additional_ids.iter().zip(others) {
            if *id != c.id
                || c.raw.ninput != circuit.raw.ninput
                || c.raw.npublic_input != circuit.raw.npublic_input
            {
                return Err("circuit statement or shared input layout mismatch".into());
            }
        }
        Ok(())
    }
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<Participant<'a, W, F, D>, String> {
        Participant::new(self.param.clone(), ctx.f, ctx.domain).map_err(|e| e.to_string())
    }
    /// Bind the packing interpretation before receiving the shared root. A
    /// degree-one layout adds no packing messages; circuit metadata still binds.
    pub fn bind(&self, t: &mut Transcript) {
        self.backend.bind(t, &self.id);
        t.write_bytes(b"layered-sumcheck/commitment-layout/v1");
        t.write_bytes(&(self.additional_ids.len() as u64).to_le_bytes());
        for id in &self.additional_ids {
            t.write_bytes(id);
        }
        t.write_bytes(&(self.geometry.sc_geom.logw_layers.len() as u64).to_le_bytes());
        for &width in &self.geometry.sc_geom.logw_layers {
            t.write_bytes(&(width as u64).to_le_bytes());
        }
    }
}

#[cfg(test)]
#[path = "../tests/circuits.rs"]
mod tests;
