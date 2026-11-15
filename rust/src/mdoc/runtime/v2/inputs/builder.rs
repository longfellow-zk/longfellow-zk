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

//! Longfellow v2 assignment builder; preserves its own field encodings.

use crate::{
    core::algebra::{AlgebraicField, Nat},
    runtime::algebra::p256::{P256Element, P256Field},
};

/// The signature circuit's assignment, in P-256 elements.
pub(super) struct AssignmentBuilder<'a> {
    field: &'a P256Field,
    pub(super) buffer: Vec<P256Element>,
}

impl<'a> AssignmentBuilder<'a> {
    pub(super) fn new(field: &'a P256Field) -> Self {
        Self {
            field,
            buffer: Vec::new(),
        }
    }

    #[inline(always)]
    fn push_bit(&mut self, bit: bool) {
        self.buffer.push(if bit {
            self.field.one()
        } else {
            self.field.zero()
        });
    }

    fn push_bits_len(&mut self, val: u64, nbits: usize) {
        let mut cur_val = val;
        for _ in 0..nbits {
            self.push_bit((cur_val & 1) != 0);
            cur_val >>= 1;
        }
    }

    pub(super) fn push_elt(&mut self, elt: &P256Element) {
        self.buffer.push(*elt);
    }

    /// The 256 bits of `nat`, least significant first.
    pub(super) fn push_nat_256_bits<N: Nat<4>>(&mut self, nat: &N) {
        for limb in nat.to_limbs() {
            self.push_bits_len(limb, 64);
        }
    }
}

cfg_prover! { mod prover; }

/// Binary assignment input methods accept bits and bit strings, never field elements.
#[derive(Default)]
pub(super) struct BinaryAssignmentBuilder {
    pub(super) buffer: Vec<bool>,
}
impl BinaryAssignmentBuilder {
    pub(super) fn new() -> Self {
        Self::default()
    }
    pub(super) fn push_bit(&mut self, bit: bool) {
        self.buffer.push(bit);
    }
    pub(super) fn push_bits_len(&mut self, value: u64, len: usize) {
        for bit in 0..len {
            self.push_bit(value >> bit & 1 != 0);
        }
    }
    pub(super) fn push_v8(&mut self, byte: u8) {
        self.push_bits_len(u64::from(byte), 8);
    }
}
