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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackedBits {
    words: Vec<u64>,
    len: usize,
}

impl PackedBits {
    fn push(&mut self, bit: bool) {
        if self.len.is_multiple_of(64) {
            self.words.push(0);
        }
        self.words[self.len / 64] |= u64::from(bit) << (self.len % 64);
        self.len += 1;
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

#[cfg(test)]
mod tests;
