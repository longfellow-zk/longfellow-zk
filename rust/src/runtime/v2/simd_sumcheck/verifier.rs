// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    proto::{
        read_bytes_32, read_field,
        sumcheck::{SumcheckProof, SumcheckProofGeometry},
    },
    transcript::{Unverified, SEAL_BYTES},
};

/// Replay messages without accepting a proof. The caller must reconstruct and
/// authenticate all affine terminal equations and the two input functionals.
pub(super) fn replay(
    products: usize,
    proof: &LayerProof<F>,
    t: &mut TranscriptRef<'_>,
) -> Result<Challenges, String> {
    if proof.rounds.len() != rounds(products)? {
        return Err("SIMD round count".into());
    }
    let f = F::new();
    let point = proof
        .rounds
        .iter()
        .map(|m| transcript::round(m, t, &f))
        .collect();
    let terminal = transcript::terminal(&proof.cross, t, &f);
    let alpha = transcript::combine(&proof.claims, t, &f);
    Ok(Challenges {
        point,
        alpha,
        terminal,
    })
}
impl Program {
    /// Reconstruct every affine equation. This stage does not authenticate it.
    pub(super) fn reduce(
        &self,
        proof: &Proof,
        t: &mut TranscriptRef<'_>,
    ) -> Result<Vec<NativeRow>, String> {
        let top = self.top_weights(t);
        let (mut equations, claim) = self.frontend_replay(proof.nonlinear, &proof.dot, top, t)?;
        let rows = adapter::verifier::reduce(&self.packing, &claim, &proof.adapter, &self.id, t)?;
        equations.extend(self.adapter_rows(rows));
        Ok(equations)
    }
    pub(super) fn frontend_replay(
        &self,
        nonlinear: E,
        dot: &LayerProof<F>,
        top: Vec<E>,
        t: &mut TranscriptRef<'_>,
    ) -> Result<(Vec<NativeRow>, adapter::Claim), String> {
        let a = top;
        transcript::nonlinear(nonlinear, t, self.packing.field());
        let challenges = replay(self.products.len(), dot, t)?;
        let mix = self
            .inputs
            .mapped()
            .map(|_| transcript::mapped_linear_mix(t, self.packing.field()));
        let (first, terminal, claim) = self.equations(&a, nonlinear, dot, &challenges, mix);
        let rows = match first {
            Some(row) => vec![row, terminal],
            None => vec![terminal],
        };
        Ok((rows, claim))
    }
}
impl Program {
    pub fn verify_complete(
        &self,
        bytes: &[u8],
        context: &[u8],
        config: PolygeroConfig,
    ) -> Result<(), String> {
        use crate::runtime::{
            algebra::range_interpolation::BinaryInterpolatorFactory,
            v2::polygero::{JointPolygeroParam, JointPolygeroVerifier},
        };
        let f = F::new();
        let domain = BinaryInterpolatorFactory::full_field(&f);
        let (participant, geometry) = self.parameter(config, &domain)?;
        let param = JointPolygeroParam::new((participant, ())).map_err(|e| e.to_string())?;
        let proof = SimdEnvelope::read(self, bytes, &geometry, config)?;
        let mut t = self.start(context, config);
        let joint = JointPolygeroVerifier::receive(&mut t.bound(&param), &proof.root);
        let rows = self.reduce(&proof.reduction, &mut t.borrow())?;
        let statements = (self.statement(rows, t.bound(&param).session())?, ());
        joint
            .reduce(&mut t.bound(&param), statements, &proof.opening)
            .map_err(|e| e.to_string())?;
        t.check_seal(proof).map(|_| ()).map_err(str::to_owned)
    }
}

#[cfg(feature = "mldsa")]
use super::shared::ScalarClaim;
#[cfg(feature = "mldsa")]
use crate::runtime::v2::proto::{dual_packing::PackingProof, sumcheck::PackedReduction};
#[cfg(feature = "mldsa")]
impl Program {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn reduce_shared(
        &self,
        proof: &PackedReduction<F>,
        packing: &PackingProof<E>,
        scalar: ScalarClaim,
        placements: &[(usize, u8)],
        cells: usize,
        t: &mut TranscriptRef<'_>,
    ) -> Result<Vec<NativeRow>, String> {
        let top = self.top_weights(t);
        let (mut rows, mut claim) = self.frontend_replay(proof.nonlinear, &proof.dot, top, t)?;
        self.combine(&mut claim, scalar, placements, cells, t)?;
        let PackingProof::TraceZero { u, a } = packing else {
            return Err("shared SIMD packing proof kind".into());
        };
        let p = adapter::Proof {
            u: u.as_slice()
                .try_into()
                .map_err(|_| "shared SIMD packing shape")?,
            a: *a,
        };
        rows.extend(self.adapter_rows(adapter::verifier::reduce(
            &self.packing,
            &claim,
            &p,
            &self.id,
            t,
        )?));
        Ok(rows)
    }
}

use crate::runtime::v2::proto::{
    polygero::{
        codec::checked_body, FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig,
        PolygeroGeometry,
    },
    simd::{SimdEnvelope, MAGIC},
    Digest,
};
impl SimdEnvelope {
    pub(super) fn read<'a>(
        p: &Program,
        bytes: &'a [u8],
        g: &PolygeroGeometry,
        config: PolygeroConfig,
    ) -> Result<Unverified<'a, Self>, String> {
        let f = F::new();
        if bytes.get(..8) != Some(MAGIC) {
            return Err("SIMD proof version".into());
        }
        let fixed = FieldProof::<E>::wire_lengths(g, 16)
            .and_then(|a| a[0].checked_add(a[1]))
            .and_then(|n| n.checked_add(32 + 16 * (1 + 2 * p.rounds() + 3 + 129)))
            .and_then(|n| {
                JointPolygeroProof::<()>::fixed_opening_len(config.t).and_then(|m| n.checked_add(m))
            })
            .ok_or("SIMD proof size overflow")?;
        let mut remaining =
            checked_body(bytes, 8, fixed, config.t, config.n).map_err(|e| e.to_string())?;
        let root = PolygeroCommitment {
            root: Digest {
                data: read_bytes_32(&mut remaining).map_err(|e| e.to_string())?,
            },
        };
        let nonlinear = read_field(&mut remaining, &f).map_err(|e| e.to_string())?;
        let sc = SumcheckProof::<F>::read(
            &mut remaining,
            &SumcheckProofGeometry::new(vec![p.rounds()]).map_err(|e| e.to_string())?,
            &f,
        )
        .map_err(|e| e.to_string())?;
        let mut u = [E::from(0); 128];
        for x in &mut u {
            *x = read_field(&mut remaining, &f).map_err(|e| e.to_string())?;
        }
        let a = read_field(&mut remaining, &f).map_err(|e| e.to_string())?;
        let opening = JointPolygeroProof::read::<std::io::Error>(
            &mut remaining,
            config.t,
            config.n,
            |b| Ok((FieldProof::read_response(b, g, &f)?, ())),
            |b, rest| b.0.read_rows(rest, g, &f),
        )
        .map_err(|e| e.to_string())?;
        let data = Self {
            root,
            reduction: Proof {
                nonlinear,
                dot: sc.layers.into_iter().next().unwrap(),
                adapter: adapter::Proof { u, a },
            },
            opening,
        };
        let mut seal = &bytes[bytes.len() - SEAL_BYTES..];
        let proof = Unverified::decoded(data, bytes, &mut seal).map_err(|e| e.to_string())?;
        if !seal.is_empty() {
            return Err("trailing SIMD proof bytes".into());
        }
        Ok(proof)
    }
}
