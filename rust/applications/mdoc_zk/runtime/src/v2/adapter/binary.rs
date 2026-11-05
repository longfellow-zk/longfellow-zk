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
        polygero::{JointPolygeroParam, Participant, PolygeroConfig, PolygeroParam},
        proto::zk_v2::{PackingLayout, ZkProofGeometry},
        random::Transcript,
        sumcheck_v2::{self},
        zk_v2::{commitment::PackingCommitment, ZkContext},
    },
};
pub(in crate::mdoc::runtime::v2) struct BinaryParticipant {
    geometry: ZkProofGeometry,
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
fn sources(c: &Circuit<F>) -> Result<Vec<usize>, String> {
    let p = p256_adapter::shared_plan();
    let private = c
        .raw
        .ninput
        .checked_sub(c.raw.npublic_input)
        .ok_or("binary public prefix")?;
    let mask = private
        .checked_sub(p.advice_bits() + 256)
        .ok_or("adapter mask layout")?;
    let device = 256 + 8 * crate::mdoc::proto::hash::constants::K_MSO_PREIMAGE_LEN + 16 + 8;
    if device + 512 > mask {
        return Err("adapter source overlap".into());
    }
    Ok((0..256)
        .chain(device..device + 512)
        .chain(mask..mask + 256)
        .map(|i| c.raw.npublic_input + i)
        .collect())
}
impl BinaryParticipant {
    pub fn new<D: EvaluationDomain<2, F>>(
        c: &Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<Self, String> {
        let sources = sources(c)?;
        let template = tree::template(
            &p256_adapter::shared_plan(),
            &sources,
            c.raw.npublic_input,
            c.raw.ninput,
        )?;
        let sc = sumcheck_v2::circuit_geometry(&[c, &template])?;
        let layout = PackingLayout::new(c.raw.ninput - c.raw.npublic_input, sc.pad_count()?, 128)?;
        let param = PolygeroParam::try_new(layout.witness_count, config, ctx.domain, ctx.f)
            .map_err(|e| e.to_string())?;
        let singleton = JointPolygeroParam::new((
            Participant::new(param.clone(), ctx.f, ctx.domain).map_err(|e| e.to_string())?,
            (),
        ))
        .map_err(|e| e.to_string())?;
        let geometry = ZkProofGeometry {
            sc_geom: sc,
            com_geom: param.geometry(),
            com_context: singleton.context(),
            packing_degree: 128,
        };
        let backend = PackingCommitment::new(ctx.f.clone(), layout, ctx.f.packing_extension())?;
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
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<2, F>>(
        &self,
        ctx: &ZkContext<'a, 2, F, D>,
    ) -> Result<Participant<'a, 2, F, D>, String> {
        Participant::new(self.param.clone(), ctx.f, ctx.domain).map_err(|e| e.to_string())
    }
    pub fn bind(&self, t: &mut Transcript) {
        self.backend.bind(t, &self.id);
        t.write_bytes(b"mdoc/adapter/shared-binary/v1");
        t.write_bytes(&self.template_id);
        for &w in &self.geometry.sc_geom.logw_layers {
            t.write_bytes(&(w as u64).to_le_bytes());
        }
    }
    fn circuit(&self, c: &Circuit<F>, public: &[bool], values: &[E]) -> Result<Circuit<F>, String> {
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
        let geometry = sumcheck_v2::circuit_geometry(&[c, &tree])?;
        if geometry != self.geometry.sc_geom {
            return Err("adapter instance geometry mismatch".into());
        }
        Ok(tree)
    }
}
cfg_prover! {#[path="binary_prover.rs"]mod prover;}
cfg_verifier! {#[path="binary_verifier.rs"]mod verifier;}
