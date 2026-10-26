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

//! Owned logical bits, independent of fields and proof protocols.

use std::ops::Range;
pub mod recipe;
#[cfg(test)]
#[path = "../tests/recipe.rs"]
mod tests;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackedBits {
    words: Vec<u64>,
    len: usize,
}

impl PackedBits {
    pub fn with_capacity(bits: usize) -> Self {
        Self {
            words: Vec::with_capacity(bits.div_ceil(64)),
            len: 0,
        }
    }

    pub fn from_le_bytes(bytes: &[u8], bit_len: usize) -> Result<Self, String> {
        if bytes.len() != bit_len.div_ceil(8) {
            return Err("logical bit byte length mismatch".into());
        }
        let mut result = Self::with_capacity(bit_len);
        for i in 0..bit_len {
            result.push((bytes[i / 8] >> (i % 8)) & 1 != 0);
        }
        Ok(result)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn get(&self, index: usize) -> bool {
        assert!(index < self.len, "logical bit index out of range");
        (self.words[index / 64] >> (index % 64)) & 1 != 0
    }

    pub fn push(&mut self, bit: bool) {
        if self.len.is_multiple_of(64) {
            self.words.push(0);
        }
        self.words[self.len / 64] |= u64::from(bit) << (self.len % 64);
        self.len += 1;
    }

    pub fn extend(&mut self, bits: &Self) {
        for i in 0..bits.len {
            self.push(bits.get(i));
        }
    }

    pub fn slice(&self, range: Range<usize>) -> Result<Self, String> {
        if range.start > range.end || range.end > self.len {
            return Err("logical bit range out of bounds".into());
        }
        Ok(range.map(|i| self.get(i)).collect())
    }

    /// Raw logical coordinates, not a field's polynomial-basis encoding.
    pub fn word128(&self, index: usize) -> u128 {
        let Some(base) = index.checked_mul(2) else {
            return 0;
        };
        let lo = self.words.get(base).copied().unwrap_or(0);
        let hi = self.words.get(base.saturating_add(1)).copied().unwrap_or(0);
        u128::from(lo) | (u128::from(hi) << 64)
    }
}

impl FromIterator<bool> for PackedBits {
    fn from_iter<T: IntoIterator<Item = bool>>(bits: T) -> Self {
        let mut result = Self::default();
        for bit in bits {
            result.push(bit);
        }
        result
    }
}
