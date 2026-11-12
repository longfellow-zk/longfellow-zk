// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked prime sumcheck with an uncommitted shared input prefix.
//! The prefix is authenticated by the caller's cross-field adapter. Only the
//! remaining prime inputs, one hiding scalar, and sumcheck pads enter this PCS.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingField, ZkField},
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            proto::sumcheck::SumcheckProof,
            transcript::TranscriptRef,
            zk::{
                joint::SelectedField, prime as prime_frontend, prime::LinearClaim, CircuitGeometry,
                ZkContext,
            },
        },
    },
};
pub(crate) struct SharedParticipant<const W: usize, F: ZkField<W> + PackingField> {
    cells: usize,
    geometry: CircuitGeometry,
    shared: usize,
    private: usize,
    id: [u8; 32],
    config: PolygeroConfig,
    _f: std::marker::PhantomData<F>,
}
impl<const W: usize, F: ZkField<W> + PackingField> SharedParticipant<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        shared: usize,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        if ctx.field().is_binary() {
            return Err("shared prime prefix requires a prime field".into());
        }
        let private = circuit
            .raw
            .ninput
            .checked_sub(circuit.raw.npublic_input)
            .ok_or("shared public prefix")?;
        if shared == 0 || shared > private {
            return Err("shared input prefix".into());
        }
        let sc = crate::runtime::v2::sumcheck::circuit_geometry(&[circuit])?;
        let count = private
            .checked_sub(shared)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_add(sc.pad_count().ok()?))
            .ok_or("shared layout overflow")?;
        let participant = SelectedField::new(count, config, ctx.domain, ctx.field().packing_id())?;
        let com_geom = participant.geometry();
        Ok(Self {
            geometry: CircuitGeometry {
                sc_geom: sc,
                com_geom,
                packing_degree: 1,
            },
            cells: count,
            shared,
            private,
            id: circuit.id,
            config,
            _f: std::marker::PhantomData,
        })
    }
    pub fn geometry(&self) -> CircuitGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &'a self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<SelectedField<'a, W, F, D, &'a Self>, String> {
        Ok(SelectedField::new(
            self.cells,
            self.config,
            ctx.domain,
            ctx.field().packing_id(),
        )?
        .with_layout(self))
    }
    /// Authenticate eta*other - R + eta*pads + mu - eta*target = 0 in the prime field.
    /// The adapter authenticates mu = eta*shared + R against the binary bits.
    pub fn finish(
        &self,
        claim: LinearClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        f: &F,
    ) -> Result<LinearStatement<F::E>, String> {
        let count = self
            .private
            .checked_add(self.geometry.sc_geom.pad_count()?)
            .ok_or("prime layout overflow")?;
        if f.is_zero(eta) || claim.weights.len() != count {
            return Err("prime shared claim shape or zero challenge".into());
        }
        let mut a = Vec::new();
        for (j, k) in claim.weights[self.shared..self.private].iter().enumerate() {
            a.push(crate::runtime::v2::polygero::PolygeroLinearTerm {
                c: 0,
                w: j,
                k: f.mulf(eta, k),
            });
        }
        let mask = self.private - self.shared;
        a.push(crate::runtime::v2::polygero::PolygeroLinearTerm {
            c: 0,
            w: mask,
            k: f.mone(),
        });
        for (i, k) in claim.weights[self.private..].iter().enumerate() {
            a.push(crate::runtime::v2::polygero::PolygeroLinearTerm {
                c: 0,
                w: mask + 1 + i,
                k: f.mulf(eta, k),
            });
        }
        Ok(LinearStatement {
            a,
            b: vec![f.subf(mu, &f.mulf(eta, &claim.target))],
            // The frontend and adapter messages already precede joint batching
            // on the shared transcript. This identifier names the source only.
            digest: crate::runtime::v2::proto::Digest { data: self.id },
        })
    }
}

cfg_prover! { #[path="prime_prover.rs"] mod prover; }
cfg_verifier! { #[path="prime_verifier.rs"] mod verifier; }

impl<const W: usize, F: ZkField<W> + PackingField> crate::runtime::v2::zk::joint::AbsorbLayout
    for SharedParticipant<W, F>
{
    fn absorb_layout(&self, t: &mut TranscriptRef<'_>) {
        super::transcript::absorb_prime(t, &self.id, self.shared);
    }
}
