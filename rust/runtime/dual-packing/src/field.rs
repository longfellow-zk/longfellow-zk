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
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) use crate::runtime::algebra::packing::binary128::dual_coordinate_numerators;
/// Explicitly owned dual to beta_j=x^j in the existing polynomial basis.
pub use crate::runtime::algebra::packing::binary128::PolynomialBasis128;
