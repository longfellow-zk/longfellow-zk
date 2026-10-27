// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Polynomial-basis packing and trace-dual coordinates. No tower is constructed.
use crate::{
    core::bits::PackedBits,
    runtime::algebra::{
        gf2_128::{Gf2_128 as E, Gf2_128Field as F},
        AlgebraicField,
    },
};

pub fn frobenius(mut value: E, squarings: usize, f: &F) -> E {
    for _ in 0..squarings {
        value = f.mulf(&value, &value);
    }
    value
}
pub fn select_bit(value: E, bit: bool) -> E {
    E::from(value.to_u128() & 0u128.wrapping_sub(u128::from(bit)))
}
pub fn pack(bits: &PackedBits) -> Vec<E> {
    (0..bits.len().div_ceil(128))
        .map(|i| E::from(bits.word128(i)))
        .collect()
}
pub fn unpack(words: &[E], bit_len: usize) -> Result<PackedBits, String> {
    if words.len() != bit_len.div_ceil(128) {
        return Err("packed word count mismatch".into());
    }
    Ok((0..bit_len)
        .map(|i| (words[i / 128].to_u128() >> (i % 128)) & 1 != 0)
        .collect())
}
pub fn trace(mut value: E, f: &F) -> E {
    let mut sum = value;
    for _ in 1..128 {
        value = f.mulf(&value, &value);
        f.add(&mut sum, &value);
    }
    sum
}
/// Explicitly owned dual to beta_j=x^j in the existing polynomial basis.
pub struct PolynomialBasis128 {
    dual: [E; 128],
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
        Self { dual }
    }
    pub fn dual(&self, index: usize) -> E {
        self.dual[index]
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
#[cfg(any(test, feature = "prover", feature = "verifier"))]
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
#[cfg(any(test, feature = "prover", feature = "verifier"))]
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
