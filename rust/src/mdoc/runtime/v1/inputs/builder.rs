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

//! Longfellow v1 assignment builder; preserves its own field encodings.

use crate::{
    core::algebra::Nat,
    mdoc::circuits::{MdocHashRuntimeField, MdocSigRuntimeField},
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

    pub(super) fn push_elt(&mut self, elt: &F::E) {
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

    pub(super) fn push_raw_bytes(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.push_bits_len(u64::from(b), 8);
        }
    }

    pub(super) fn push_pad(&mut self, pad_elt: F::E, count: usize) {
        self.buffer.extend(std::iter::repeat_n(pad_elt, count));
    }
}

impl<F: MdocHashRuntimeField> AssignmentBuilder<'_, F> {
    pub(super) fn push_u128(&mut self, val: u128) {
        self.buffer.push(self.field.u128_to_element(val));
    }
}

impl<F: MdocSigRuntimeField> AssignmentBuilder<'_, F> {
    pub(super) fn push_nat_elt<const W_NAT: usize, N: Nat<W_NAT>>(&mut self, val: &N) {
        let mut bytes = val.to_bytes_le();
        bytes.resize(32, 0);
        let el = self.field.bytes_to_element(&bytes).unwrap();
        self.buffer.push(el);
    }
}

cfg_prover! {
    use crate::mdoc::proto::config::K_SIG_MAC_BIT_PLUCKER_V1;


    impl<
            F: crate::core::algebra::BareField
                + crate::core::algebra::AlgebraicField
                + crate::core::algebra::HasLookupPoints,
        > AssignmentBuilder<'_, F>
    {
        fn pack_bits_to_elements_legacy<const PLUCKER_WIDTH: usize>(
            &self,
            bits: &[bool],
        ) -> Vec<F::E> {
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
                elts.push(self.field.lookup_point(1 << PLUCKER_WIDTH, v));
            }
            elts
        }

        fn push_value_plucked_legacy<const PLUCKER_WIDTH: usize, const BIT_LEN: usize>(
            &mut self,
            val: u128,
        ) {
            let mut bits = [false; BIT_LEN];
            let mut cur_val = val;
            for item in &mut bits {
                *item = (cur_val & 1) != 0;
                cur_val >>= 1;
            }
            let elts = self.pack_bits_to_elements_legacy::<PLUCKER_WIDTH>(&bits);
            self.buffer.extend(elts);
        }
    }

    impl<F: MdocHashRuntimeField> AssignmentBuilder<'_, F> {
        pub(super) fn push_v32_legacy(&mut self, val: u32) {
            let mut cur_val = val;
            for _ in 0..8 {
                let val_chunk = (cur_val & 0xf) as usize;
                let plucked = (val_chunk << 1) ^ 15;
                let mut pt = self.field.u128_to_element(0u128);
                for (j, &basis_val) in crate::core::algebra::GF2_16_BASIS_V1.iter().enumerate() {
                    if (plucked & (1 << j)) != 0 {
                        pt = self.field.addf(&pt, &self.field.u128_to_element(basis_val));
                    }
                }
                self.buffer.push(pt);
                cur_val >>= 4;
            }
        }

    }

    impl<F: MdocSigRuntimeField> AssignmentBuilder<'_, F> {
        pub(super) fn push_plucked_128_legacy(&mut self, val: u128) {
            self.push_value_plucked_legacy::<{ K_SIG_MAC_BIT_PLUCKER_V1 }, 128>(val);
        }
    }
}
