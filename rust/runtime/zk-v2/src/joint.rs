// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit metadata shared by standalone proofs and joint field commitments.
use super::{commitment::PackingCommitment, context::prepare_layout, ZkContext, ZkProofGeometry};
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
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let (geometry, param, backend) =
            prepare_layout(circuit, config, ctx.f.packing_extension(), ctx)?;
        Ok(Self {
            geometry,
            #[cfg(any(test, feature = "prover"))]
            config,
            param,
            backend,
            id: circuit.id,
        })
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
    /// degree-one input layout adds no packing metadata or transcript messages.
    pub fn bind(&self, t: &mut Transcript) {
        self.backend.bind(t, &self.id);
    }
}
