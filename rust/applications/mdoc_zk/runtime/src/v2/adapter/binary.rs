// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One packed source array and one layered sumcheck for hash and adapter terms.
use crate::{
    core::proto::v2::Circuit,
    mdoc::circuits::p256_adapter::{self, tree},
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            EvaluationDomain, PackingField,
        },
        v2::{
            polygero::{PolygeroConfig, PolygeroParam},
            proto::zk::CircuitGeometry,
            sumcheck,
            transcript::TranscriptRef,
            zk::{joint::SelectedField, packing_commitment::PackingCommitment, ZkContext},
        },
    },
};
pub(in crate::mdoc::runtime::v2) struct BinaryParticipant {
    geometry: CircuitGeometry,
    backend: PackingCommitment<F>,
    param: PolygeroParam,
    id: [u8; 32],
    template_id: [u8; 32],
    #[cfg(any(test, feature = "prover"))]
    config: PolygeroConfig,
    sources: Vec<usize>,
    npublic: usize,
    ninput: usize,
}
/// The archive and compiler define this shared layout. R and quotient pads are
/// last; the tree consumes every pad while presentation predicates use the rest.
pub(super) fn sources(npublic: usize, ninput: usize) -> Result<Vec<usize>, String> {
    let p = p256_adapter::shared_plan();
    let private = ninput.checked_sub(npublic).ok_or("binary public prefix")?;
    let mask = private
        .checked_sub(p.advice_bits() + 256)
        .ok_or("adapter mask layout")?;
    // Between issuer digest and device coordinates are the padded MSO preimage,
    // its length, and the one-byte SHA block count. This is the allocation
    // order in hash::allocate, also used by the private assignment encoder.
    use crate::mdoc::proto::hash::constants::{K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN};
    let device = 256 + 8 * K_MSO_PREIMAGE_LEN + K_HASH_INDEX_BITS + 8;
    if device + 512 > mask {
        return Err("adapter source overlap".into());
    }
    Ok((0..256)
        .chain(device..device + 512)
        .chain(mask..mask + 256)
        .map(|i| npublic + i)
        .collect())
}
impl BinaryParticipant {
    pub(crate) fn new<D: EvaluationDomain<2, F>>(
        c: &Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<Self, String> {
        let sources = sources(c.raw.npublic_input, c.raw.ninput)?;
        let template = tree::template(
            &p256_adapter::shared_plan(),
            &sources,
            c.raw.npublic_input,
            c.raw.ninput,
        )?;
        let (geometry, param, backend) = crate::runtime::v2::zk::prepare_layout(
            c,
            &[&template],
            config,
            ctx.field().packing_extension(),
            ctx,
        )?;
        Ok(Self {
            geometry,
            backend,
            param,
            #[cfg(any(test, feature = "prover"))]
            config,
            id: c.id,
            template_id: template.id,
            sources,
            npublic: c.raw.npublic_input,
            ninput: c.raw.ninput,
        })
    }
    pub(crate) fn geometry(&self) -> CircuitGeometry {
        self.geometry.clone()
    }
    pub(crate) fn participant<'a, D: EvaluationDomain<2, F>>(
        &'a self,
        ctx: &ZkContext<'a, 2, F, D>,
    ) -> Result<SelectedField<'a, 2, F, D, &'a Self>, String> {
        Ok(
            SelectedField::from_parameter(
                self.param.clone(),
                ctx.domain,
                ctx.field().packing_id(),
            )?
            .with_layout(self),
        )
    }
    fn circuit(
        &self,
        c: &Circuit<F>,
        public: &[bool],
        values: &[E],
    ) -> Result<crate::core::proto::v2::RawCircuit<F>, String> {
        if c.id != self.id
            || c.raw.ninput != self.ninput
            || c.raw.npublic_input != self.npublic
            || public.len() != self.npublic
        {
            return Err("binary circuit statement mismatch".into());
        }
        let tree = tree::program(
            &p256_adapter::shared_plan(),
            &self.sources,
            self.npublic,
            self.ninput,
            values,
        )?;
        let geometry = sumcheck::circuit_geometry(&[&c.raw, &tree])?;
        if geometry != self.geometry.sc_geom {
            return Err("adapter instance geometry mismatch".into());
        }
        Ok(tree)
    }
}
cfg_prover! {#[path="binary_prover.rs"]mod prover;}
cfg_verifier! {#[path="binary_verifier.rs"]mod verifier;}

impl crate::runtime::v2::zk::joint::AbsorbLayout for BinaryParticipant {
    fn absorb_layout(&self, t: &mut TranscriptRef<'_>) {
        self.backend.absorb(t, &self.id);
        super::transcript::absorb_binary(t, &self.template_id, &self.geometry.sc_geom.logw_layers);
    }
}
