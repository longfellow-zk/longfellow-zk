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
    mdoc::{
        circuits::{MdocHashRuntimeField, MdocSigRuntimeField},
        proto::config::{K_HASH_V8_BIT_PLUCKER, K_SIG_MAC_BIT_PLUCKER},
    },
};

pub(super) struct AssignmentBuilder<
    'a,
    F: crate::core::algebra::BareField + crate::core::algebra::AlgebraicField,
> {
    pub(super) field: &'a F,
    buffer: Vec<F::E>,
    pub(super) boolean: bool,
}

impl<'a, F: crate::core::algebra::BareField + crate::core::algebra::AlgebraicField>
    AssignmentBuilder<'a, F>
{
    pub(super) fn new(field: &'a F) -> Self {
        Self {
            field,
            buffer: Vec::new(),
            boolean: false,
        }
    }

    pub(super) fn new_boolean(field: &'a F) -> Self {
        Self {
            field,
            buffer: Vec::new(),
            boolean: true,
        }
    }
    pub(super) fn push_elt(&mut self, elt: &F::E) {
        if self.boolean {
            assert!(
                *elt == self.field.zero() || *elt == self.field.one(),
                "nonboolean circuit input"
            );
        }
        self.buffer.push(elt.clone());
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
        if self.boolean {
            for bit in bits {
                self.push_bit(bit);
            }
            return;
        }
        let elts = self.pack_bits_to_elements::<PLUCKER_WIDTH>(&bits);
        self.buffer.extend(elts);
    }
}

impl<F: MdocHashRuntimeField> AssignmentBuilder<'_, F> {
    pub(super) fn push_v8(&mut self, byte: u8) {
        self.push_value_plucked::<{ K_HASH_V8_BIT_PLUCKER }, 8>(u128::from(byte));
    }

    /// Supply the MAC field value in the circuit's selected input representation.
    pub(super) fn push_mac_field(&mut self, val: u128) {
        if self.boolean {
            for i in 0..128 {
                self.push_bit((val >> i) & 1 != 0);
            }
            return;
        }
        self.buffer.push(self.field.u128_to_element(val));
    }
}

impl<F: MdocSigRuntimeField> AssignmentBuilder<'_, F> {
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
    use crate::mdoc::proto::config::{K_HASH_V256_BIT_PLUCKER, K_SHA_BIT_PLUCKER};

    impl<F: crate::core::algebra::BareField + crate::core::algebra::AlgebraicField>
        AssignmentBuilder<'_, F>
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

    impl<
            F: crate::core::algebra::BareField
                + crate::core::algebra::AlgebraicField
                + crate::core::algebra::HasLookupPoints,
        > AssignmentBuilder<'_, F>
    {
        fn push_nat_plucked<const PLUCKER_WIDTH: usize, const W: usize, N: Nat<W>>(
            &mut self,
            nat: &N,
        ) {
            let mut bytes = nat.to_bytes_le();
            bytes.resize(W * 8, 0);

            let mut bits = vec![false; W * 64];
            for (i, &byte) in bytes.iter().enumerate() {
                let mut cur_byte = byte;
                for k in 0..8 {
                    bits[i * 8 + k] = (cur_byte & 1) != 0;
                    cur_byte >>= 1;
                }
            }

                        if self.boolean {
                for bit in bits {
                    self.push_bit(bit);
                }
                return;
            }
            let elts = self.pack_bits_to_elements::<PLUCKER_WIDTH>(&bits);
            self.buffer.extend(elts);
        }

    }

    impl<F: MdocHashRuntimeField> AssignmentBuilder<'_, F> {
        pub(super) fn push_v32(&mut self, val: u32) {
            self.push_value_plucked::<{ K_SHA_BIT_PLUCKER }, 32>(u128::from(val));
        }

        pub(super) fn push_nat256<N: Nat<4>>(&mut self, nat: &N) {
            self.push_nat_plucked::<{ K_HASH_V256_BIT_PLUCKER }, 4, N>(nat);
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
