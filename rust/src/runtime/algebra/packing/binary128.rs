// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Polynomial-basis trace pairing and Boolean transpose kernels.
use crate::runtime::algebra::{
    gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    AlgebraicField,
};
/// Newton's identities for P=x^128+x^7+x^2+x+1 give Tr(x^j)=1 only
/// at j=121 and j=127 for 0<=j<128. Trace is GF2-linear, so two coordinates
/// suffice; no Frobenius table or data-dependent lookup is needed.
pub(super) fn trace(value: E) -> E {
    let bits = value.to_u128();
    E::from(((bits >> 121) ^ (bits >> 127)) & 1)
}

/// The polynomial-basis trace dual has the same closed form used by the
/// transpose below. Its denominator is P'(x)=x^6+1. Deriving it directly
/// avoids constructing and inverting a 128-by-128 trace-pairing matrix.
pub(super) fn dual_basis(f: &F) -> Vec<E> {
    let denominator_inverse = f.invert(&E::from((1 << 6) | 1));
    (0..128)
        .map(|j| {
            let mut numerator = 1u128 << (127 - j);
            if j < 7 {
                numerator ^= 1 << (6 - j);
            }
            if j < 2 {
                numerator ^= 1 << (1 - j);
            }
            if j == 0 {
                numerator ^= 1;
            }
            f.mulf(&E::from(numerator), &denominator_inverse)
        })
        .collect()
}

/// For R_j=sum_h beta_h*r_jh, return N_h such that
/// sum_j dual_j*r_jh = dual_127*N_h. Pad absent columns by zero.
///
/// For P=x^128+x^7+x^2+x+1, the polynomial-basis dual is
/// dual_j=(x^(127-j)+[j<7]x^(6-j)+[j<2]x^(1-j)+[j=0])/P'(x).
/// Reversing the coefficient indices before transposition packs these four
/// terms as u ^ (u>>121) ^ (u>>126) ^ (u>>127). The common denominator
/// dual_127=1/(x^6+1) can be applied once after a whole field sum.
pub(super) fn dual_coordinate_numerators(row: &[E]) -> [E; 128] {
    assert!(row.len() <= 128);
    let mut coordinates = [0u128; 128];
    for (j, coefficient) in row.iter().enumerate() {
        coordinates[127 - j] = coefficient.to_u128();
    }
    transpose_step::<64>(&mut coordinates);
    transpose_step::<32>(&mut coordinates);
    transpose_step::<16>(&mut coordinates);
    transpose_step::<8>(&mut coordinates);
    transpose_step::<4>(&mut coordinates);
    transpose_step::<2>(&mut coordinates);
    transpose_step::<1>(&mut coordinates);
    coordinates.map(|u| E::from(u ^ (u >> 121) ^ (u >> 126) ^ (u >> 127)))
}

/// Swap the off-diagonal bit blocks at one scale. The indices and masks are
/// fixed; this transpose also needs no lookup indexed by witness data.
fn transpose_step<const SHIFT: usize>(rows: &mut [u128; 128]) {
    let mask = u128::MAX / ((1u128 << SHIFT) + 1);
    for base in (0..128).step_by(2 * SHIFT) {
        for k in base..base + SHIFT {
            let swap = ((rows[k] >> SHIFT) ^ rows[k + SHIFT]) & mask;
            rows[k] ^= swap << SHIFT;
            rows[k + SHIFT] ^= swap;
        }
    }
}
