// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Polynomial-basis trace pairing and Boolean transpose kernels.
use crate::runtime::algebra::{
    gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    AlgebraicField,
};
fn trace(mut x: E, f: &F) -> E {
    let mut s = x;
    for _ in 1..128 {
        x = f.mulf(&x, &x);
        f.add(&mut s, &x);
    }
    s
}
pub struct PolynomialBasis128 {
    dual: [E; 128],
    trace_mask: u128,
}
impl PolynomialBasis128 {
    pub fn new(f: &F) -> Self {
        // Tr(x^(j+k)) depends only on j+k, so only 255 traces are needed.
        let mut power = f.one();
        let traces: [bool; 255] = std::array::from_fn(|_| {
            let bit = trace(power, f) == f.one();
            power = f.mulf(&power, &E::from(2));
            bit
        });
        let mut rows: [u128; 128] = std::array::from_fn(|j| {
            (0..128).fold(0u128, |row, k| row | (u128::from(traces[j + k]) << k))
        });
        let mut inverse: [u128; 128] = std::array::from_fn(|j| 1u128 << j);
        for column in 0..128 {
            let pivot = (column..128)
                .find(|&r| (rows[r] >> column) & 1 != 0)
                .expect("nondegenerate trace pairing");
            rows.swap(column, pivot);
            inverse.swap(column, pivot);
            for row in 0..128 {
                if row != column && (rows[row] >> column) & 1 != 0 {
                    rows[row] ^= rows[column];
                    inverse[row] ^= inverse[column];
                }
            }
        }
        let dual = std::array::from_fn(|j| {
            E::from((0..128).fold(0u128, |value, k| value | (((inverse[k] >> j) & 1) << k)))
        });
        let trace_mask = (0..128).fold(0, |mask, k| mask | (u128::from(traces[k]) << k));
        Self { dual, trace_mask }
    }
    pub fn dual(&self, index: usize) -> E {
        self.dual[index]
    }
    /// The absolute trace is a fixed parity of polynomial coordinates.
    pub fn trace_bit(&self, value: E) -> bool {
        (value.to_u128() & self.trace_mask).count_ones() & 1 != 0
    }
}

/// For R_j=sum_h beta_h*r_jh, return N_h such that
/// sum_j dual_j*r_jh = dual_127*N_h. Pad absent columns by zero.
///
/// For P=x^128+x^7+x^2+x+1, the polynomial-basis dual is
/// dual_j=(x^(127-j)+[j<7]x^(6-j)+[j<2]x^(1-j)+[j=0])/P'(x).
/// Reversing the coefficient indices before transposition packs these four
/// terms as u ^ (u>>121) ^ (u>>126) ^ (u>>127). The common denominator
/// dual_127=1/(x^6+1) can be applied once after a whole field sum.
pub(crate) fn dual_coordinate_numerators(row: &[E]) -> [E; 128] {
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
