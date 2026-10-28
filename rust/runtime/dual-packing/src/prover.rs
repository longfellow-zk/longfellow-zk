// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trace-zero messages U, followed by the masked scalar A from the paper.
use super::{
    field::{self, PolynomialBasis128},
    BitLinearClaim, DualPacking128Proof, PackedLinearClaim, DUAL_PACKING_COORDINATES,
    DUAL_PACKING_FREE_MASKS, DUAL_PACKING_MASK_CELLS,
};
use crate::{
    core::bits::PackedBits,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            AlgebraicField, RuntimeField,
        },
        random::{RandomEngine, Transcript},
    },
};
pub struct DualPackingMaskValues {
    free: [E; DUAL_PACKING_FREE_MASKS],
    r: E,
    b: E,
}
impl DualPackingMaskValues {
    pub fn sample(rng: &mut impl RandomEngine, f: &F) -> Self {
        let free = std::array::from_fn(|_| E::from(rng.u128()));
        let r = E::from(rng.u128());
        Self {
            free,
            r,
            b: f.mulf(&r, &r),
        }
    }
    pub fn cells(&self) -> [E; DUAL_PACKING_MASK_CELLS] {
        std::array::from_fn(|i| match i {
            DUAL_PACKING_FREE_MASKS => self.r,
            index if index == DUAL_PACKING_FREE_MASKS + 1 => self.b,
            _ => self.free[i],
        })
    }
    pub(super) fn coordinates(&self, f: &F) -> [E; DUAL_PACKING_COORDINATES] {
        let mut result = [f.zero(); DUAL_PACKING_COORDINATES];
        result[1..].copy_from_slice(&self.free);
        for (j, t) in self.free.iter().enumerate() {
            f.fma(&mut result[0], &E::from(1u128 << (j + 1)), t);
        }
        result
    }
}
/// B_k=sum_i D_ik*X_i, where D_ik=sum_j alpha_j*digit_k(R_ij).
/// Only public coefficient rows are transposed. No Frobenius orbit is computed.
pub(super) fn components(
    basis: &PolynomialBasis128,
    weights: &[E],
    bits: &PackedBits,
    f: &F,
) -> [E; DUAL_PACKING_COORDINATES] {
    let mut accum = std::array::from_fn::<_, DUAL_PACKING_COORDINATES, _>(|_| f.zero_accum());
    for (i, row) in weights.chunks(DUAL_PACKING_COORDINATES).enumerate() {
        let numerators = field::dual_coordinate_numerators(row);
        let word = E::from(bits.word128(i));
        for (a, coefficient) in accum.iter_mut().zip(&numerators) {
            f.mac(a, &word, coefficient);
        }
    }
    accum.map(|a| f.mulf(&basis.dual(127), &f.accum_reduce(&a)))
}
#[allow(clippy::too_many_arguments)]
pub fn reduce(
    basis: &PolynomialBasis128,
    claim: &BitLinearClaim,
    bits: &PackedBits,
    auxiliary: &[E],
    masks: DualPackingMaskValues,
    context: &[u8],
    ts: &mut Transcript,
    f: &F,
) -> Result<(DualPacking128Proof, [PackedLinearClaim; 2]), String> {
    claim.validate()?;
    if bits.len() != claim.weights.len() || auxiliary.len() != claim.auxiliary_count {
        return Err("dual packing witness shape mismatch".into());
    }
    let target = claim.rhs.evaluate(auxiliary, f)?;
    let t = masks.coordinates(f);
    let b = components(basis, &claim.weights, bits, f);
    let u = std::array::from_fn(|k| {
        f.addf(
            &f.addf(&b[k], &f.mulf(&basis.dual(k), &target)),
            &f.addf(&t[k], &f.mulf(&t[k], &t[k])),
        )
    });
    super::validate_traces(basis, &u)?;
    super::transcript::begin(claim, context, ts, f);
    let delta = super::transcript::challenge(&u, ts, f);
    let mut a = masks.r;
    for (d, mask) in delta.iter().zip(&t) {
        f.fma(&mut a, d, mask);
    }
    super::transcript::finish(a, ts, f);
    let proof = DualPacking128Proof { u, a };
    let result = super::reconstruct(basis, claim, &proof, &delta, f);
    Ok((proof, result))
}
