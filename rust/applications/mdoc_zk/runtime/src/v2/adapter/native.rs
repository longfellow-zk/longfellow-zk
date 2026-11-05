// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked native sumcheck with an uncommitted shared input prefix.
//! The prefix is authenticated by the caller's cross-field adapter. Only the
//! remaining native inputs, one hiding scalar, and sumcheck pads enter this PCS.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, ZkField},
        polygero::{LinearStatement, Participant, PolygeroConfig, PolygeroParam},
        proto::sumcheck_v2::SumcheckProof,
        random::Transcript,
        zk_v2::{
            native::{self as native_frontend, LinearClaim},
            ZkContext, ZkProofGeometry,
        },
    },
};
pub(crate) struct SharedParticipant<const W: usize, F: ZkField<W>> {
    param: PolygeroParam,
    geometry: ZkProofGeometry,
    shared: usize,
    private: usize,
    id: [u8; 32],
    #[cfg(any(test, feature = "prover"))]
    config: PolygeroConfig,
    _f: std::marker::PhantomData<F>,
}
impl<const W: usize, F: ZkField<W>> SharedParticipant<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        shared: usize,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        if ctx.f.is_binary() {
            return Err("shared native prefix requires a prime field".into());
        }
        let private = circuit
            .raw
            .ninput
            .checked_sub(circuit.raw.npublic_input)
            .ok_or("shared public prefix")?;
        if shared == 0 || shared > private {
            return Err("shared input prefix".into());
        }
        let sc = crate::runtime::sumcheck_v2::circuit_geometry(&[circuit])?;
        let count = private
            .checked_sub(shared)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_add(sc.pad_count().ok()?))
            .ok_or("shared layout overflow")?;
        let param =
            PolygeroParam::try_new(count, config, ctx.domain, ctx.f).map_err(|e| e.to_string())?;
        Ok(Self {
            geometry: ZkProofGeometry {
                sc_geom: sc,
                com_context: crate::runtime::polygero::JointPolygeroParam::new((
                    Participant::new(param.clone(), ctx.f, ctx.domain)
                        .map_err(|e| e.to_string())?,
                    (),
                ))
                .map_err(|e| e.to_string())?
                .context(),
                com_geom: param.geometry(),
                packing_degree: 1,
            },
            param,
            shared,
            private,
            id: circuit.id,
            #[cfg(any(test, feature = "prover"))]
            config,
            _f: std::marker::PhantomData,
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
    pub fn bind(&self, t: &mut Transcript) {
        t.write_bytes(b"native-shared-prefix/joint/v1");
        t.write_bytes(&self.id);
        t.write_bytes(&(self.shared as u64).to_le_bytes());
    }
    /// Authenticate eta*other - R + eta*pads + mu - eta*target = 0 natively.
    /// The adapter authenticates mu = eta*shared + R against the binary bits.
    pub fn finish(
        &self,
        claim: LinearClaim<F::E>,
        eta: &F::E,
        mu: &F::E,
        t: &mut Transcript,
        f: &F,
    ) -> Result<LinearStatement<F::E>, String> {
        let count = self
            .private
            .checked_add(self.geometry.sc_geom.pad_count()?)
            .ok_or("native layout overflow")?;
        if f.is_zero(eta) || claim.weights.len() != count {
            return Err("native shared claim shape or zero challenge".into());
        }
        let mut a = Vec::new();
        for (j, k) in claim.weights[self.shared..self.private].iter().enumerate() {
            a.push(crate::runtime::polygero::PolygeroLinearTerm {
                c: 0,
                w: j,
                k: f.mulf(eta, k),
            });
        }
        let mask = self.private - self.shared;
        a.push(crate::runtime::polygero::PolygeroLinearTerm {
            c: 0,
            w: mask,
            k: f.mone(),
        });
        for (i, k) in claim.weights[self.private..].iter().enumerate() {
            a.push(crate::runtime::polygero::PolygeroLinearTerm {
                c: 0,
                w: mask + 1 + i,
                k: f.mulf(eta, k),
            });
        }
        Ok(LinearStatement {
            a,
            b: vec![f.subf(mu, &f.mulf(eta, &claim.target))],
            digest: crate::runtime::zk_v2::transcript::statement_digest(t),
        })
    }
}

cfg_prover! { #[path="native_prover.rs"] mod prover; }
cfg_verifier! { #[path="native_verifier.rs"] mod verifier; }
