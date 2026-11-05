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
    core::algebra::Nat,
    mdoc::{circuits::MdocSigRuntimeField, proto::config::K_SIG_MAC_BIT_PLUCKER},
};

pub(super) struct AssignmentBuilder<
    'a,
    F: crate::core::algebra::BareField + crate::core::algebra::AlgebraicField,
> {
    pub(super) field: &'a F,
    buffer: Vec<F::E>,
}

impl<'a, F: crate::core::algebra::BareField + crate::core::algebra::AlgebraicField>
    AssignmentBuilder<'a, F>
{
    pub(super) fn new(field: &'a F) -> Self {
        Self {
            field,
            buffer: Vec::new(),
        }
    }

    pub(super) fn into_inner(self) -> Vec<F::E> {
        self.buffer
    }

    #[inline(always)]
    fn push_bit(&mut self, bit: bool) {
        self.buffer.push(if bit {
            self.field.one()
        } else {
            self.field.zero()
        });
    }

    pub(super) fn push_bits_len(&mut self, val: u64, nbits: usize) {
        let mut cur_val = val;
        for _ in 0..nbits {
            self.push_bit((cur_val & 1) != 0);
            cur_val >>= 1;
        }
    }
}

impl<
        F: crate::core::algebra::BareField
            + crate::core::algebra::AlgebraicField
            + crate::core::algebra::HasLookupPoints,
    > AssignmentBuilder<'_, F>
{
    fn pack_bits_to_elements<const PLUCKER_WIDTH: usize>(&self, bits: &[bool]) -> Vec<F::E> {
        let num_chunks = bits.len().div_ceil(PLUCKER_WIDTH);
        let mut elts = Vec::with_capacity(num_chunks);
        for i in 0..num_chunks {
            let mut v = 0usize;
            for j in 0..PLUCKER_WIDTH {
                let idx = i * PLUCKER_WIDTH + j;
                if idx < bits.len() && bits[idx] {
                    v |= 1 << j;
                }
            }
            elts.push(crate::circuits::bit_plucker::encoding_point::<
                F,
                PLUCKER_WIDTH,
            >(self.field, v));
        }
        elts
    }

    fn push_value_plucked<const PLUCKER_WIDTH: usize, const BIT_LEN: usize>(&mut self, val: u128) {
        let mut bits = [false; BIT_LEN];
        let mut cur_val = val;
        for item in &mut bits {
            *item = (cur_val & 1) != 0;
            cur_val >>= 1;
        }
        let elts = self.pack_bits_to_elements::<PLUCKER_WIDTH>(&bits);
        self.buffer.extend(elts);
    }
}

impl<F: MdocSigRuntimeField> AssignmentBuilder<'_, F> {
    pub(super) fn push_elt(&mut self, elt: &F::E) {
        self.buffer.push(elt.clone());
    }

    pub(super) fn push_nat_256_bits<N: Nat<4>>(&mut self, nat: &N) {
        let mut bytes = nat.to_bytes_le();
        bytes.resize(32, 0);
        for &b in &bytes {
            self.push_bits_len(u64::from(b), 8);
        }
    }

    pub(super) fn push_plucked_128(&mut self, val: u128) {
        self.push_value_plucked::<{ K_SIG_MAC_BIT_PLUCKER }, 128>(val);
    }
}

cfg_prover! {
    impl<F: MdocSigRuntimeField> AssignmentBuilder<'_, F>
    {
        pub(super) fn push_ecdsa_given(
            &mut self,
            given: &crate::circuits::ecdsa2::concrete::ConcreteGiven<F>,
        ) {
            given.push_elements(|elt| self.push_elt(elt));
        }

        pub(super) fn push_ecdsa_derived(
            &mut self,
            derived: &crate::circuits::ecdsa2::concrete::ConcreteDerived<F>,
        ) {
            derived.push_elements(|elt| self.push_elt(elt));
        }
    }



    impl BinaryAssignmentBuilder {
        pub(super) fn push_v32(&mut self, val: u32) {
            self.push_bits_len(u64::from(val),32);
        }

        pub(super) fn push_nat256<N: Nat<4>>(&mut self, nat: &N) {
            let mut bytes=nat.to_bytes_le(); bytes.resize(32,0);
            for byte in bytes { self.push_v8(byte); }
        }

        pub(super) fn push_sha256_derived(
            &mut self,
            derived: &crate::circuits::sha256::concrete::ConcreteDerived,
        ) {
            for val in derived.modern_elements() {
                self.push_v32(val);
            }
        }

        pub(super) fn push_sha256msg_derived(
            &mut self,
            derived: &crate::circuits::sha256msg::concrete::ConcreteDerived,
        ) {
            for sha in &derived.sha_derived {
                self.push_sha256_derived(sha);
            }
        }
    }

}

/// Binary assignment input methods accept bits and bit strings, never field elements.
#[derive(Default)]
pub(super) struct BinaryAssignmentBuilder {
    buffer: Vec<bool>,
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
    pub(super) fn push_u128(&mut self, value: u128) {
        for byte in value.to_le_bytes() {
            self.push_v8(byte);
        }
    }
    pub(super) fn into_inner(self) -> Vec<bool> {
        self.buffer
    }
}
