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

use super::shape::Derived;
use crate::{
    circuits::{
        analog_adder::FieldWrappingSum,
        arithmetic::Arithmetic,
        bitvec::{Bitvec, BitvecLogic, V256, V32, V64, V8},
        boolean::{Bitw, Boolean},
        sha256::{Derived as Sha256Derived, Sha256},
    },
    compile::logic::{Eltw, Logic},
};

pub struct Given<L: Logic, const S: usize> {
    pub padded_preimage: Vec<V8<L>>,
    pub nblocks: Bitvec<L, S>,
    pub length_bytes: V64<L>,
    /// The expected digest in big-endian byte order. Each entry must be
    /// a packing of eight Boolean values, as produced by `pack_digest`.
    pub expected_hash: [Eltw<L>; 32],
}

/// A digest given as 256 bits, least significant first, as the 32 packed
/// bytes of its big-endian encoding.
pub fn pack_digest<L: Logic>(logic: &L, bits: &V256<L>) -> [Eltw<L>; 32] {
    let arith = Arithmetic::new(logic);
    let le = bits.as_array();
    std::array::from_fn(|m| arith.pack_byte(&le[8 * (31 - m)..8 * (32 - m)]))
}

pub struct Sha256Msg<'a, L: Logic, const MAX_BLOCKS: usize>
where L::F: FieldWrappingSum
{
    logic: &'a L,
    sha: Sha256<'a, L>,
    bv: BitvecLogic<'a, L>,
    boolean: Boolean<'a, L>,
}

impl<'a, L: Logic, const MAX_BLOCKS: usize> Sha256Msg<'a, L, MAX_BLOCKS>
where L::F: FieldWrappingSum
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            sha: Sha256::new(logic),
            bv: BitvecLogic::new(logic),
            boolean: Boolean::new(logic),
        }
    }

    fn initial_context(&self) -> [V32<L>; 8] {
        let initial = [
            0x6a09e667u32,
            0xbb67ae85u32,
            0x3c6ef372u32,
            0xa54ff53au32,
            0x510e527fu32,
            0x9b05688cu32,
            0x1f83d9abu32,
            0x5be0cd19u32,
        ];
        std::array::from_fn(|i| self.bv.of_u32(initial[i]))
    }

    /// Asserts that the SHA-256 compression is correctly executed for
    /// all blocks, and that any idle blocks beyond `nblocks` are
    /// properly padded with zero bytes.
    fn assert_intermediate_hashes(
        &self,
        input_bytes: &[V8<L>],
        derived: &[Sha256Derived<V32<L>>],
    ) -> L::Assertions {
        let mut h = self.initial_context();
        self.logic
            .assert_mapi("assert_intermediate_hashes", 0..MAX_BLOCKS, |b| {
                let inb = &input_bytes[64 * b..64 * (b + 1)];
                let tmp: [V32<L>; 16] = std::array::from_fn(|i| {
                    let mut word_bits = Vec::with_capacity(32);
                    word_bits.extend(inb[4 * i + 3].iter().cloned());
                    word_bits.extend(inb[4 * i + 2].iter().cloned());
                    word_bits.extend(inb[4 * i + 1].iter().cloned());
                    word_bits.extend(inb[4 * i].iter().cloned());
                    V32::new(word_bits)
                });

                let block_given = crate::circuits::sha256::Given {
                    input_block: tmp,
                    h0: h.clone(),
                };
                let block_assertion = self.sha.assert_transform_block(&block_given, &derived[b]);
                h = derived[b].h1.clone();
                block_assertion
            })
    }

    /// `selector[b]` is true exactly when `nblocks == b + 1`, that is, when
    /// block `b` ends the message. At most one selector is true.
    fn block_selector<const S: usize>(&self, nblocks: &Bitvec<L, S>) -> Vec<Bitw<L>> {
        (0..MAX_BLOCKS)
            .map(|b| self.bv.eqb(nblocks, &self.bv.of_u64((b + 1) as u64)))
            .collect()
    }

    /// Asserts that the SHA-256 hash output of the active message
    /// (located at the end of block `nblocks - 1`) matches the expected
    /// hash `expected_hash`.
    ///
    /// Each block's chaining value is compared under its selector, so no
    /// multiplexer waits for the selector while every block's chaining value
    /// is carried up the circuit. `assert_nblocks` requires one selector to
    /// be true.
    fn assert_final_hash<const S: usize>(
        &self,
        expected_hash: &[Eltw<L>; 32],
        nblocks: &Bitvec<L, S>,
        derived: &[Sha256Derived<V32<L>>],
    ) -> L::Assertions {
        let arith = Arithmetic::new(self.logic);
        let expected_le: Vec<_> = expected_hash.iter().rev().cloned().collect();
        let selector = self.block_selector(nblocks);
        self.logic.assert_mapi("hash_eq", 0..MAX_BLOCKS, |b| {
            // The chaining value as a v256 in reverse word order.
            let h1 = &derived[b].h1;
            let hash = self
                .bv
                .from_fn::<256, _>(|i| h1[7 - i / 32][i % 32].clone());
            arith.assert_eq_packed_bytes_when(
                "block_hash_eq",
                &selector[b],
                hash.as_array(),
                &expected_le,
            )
        })
    }

    /// Asserts that `nblocks` is within valid range limits: 0 <
    /// `nblocks` <= `MAX_BLOCKS`, and mathematically consistent with
    /// the message's byte length `length_bytes`.
    pub fn assert_nblocks<const S: usize>(
        &self,
        nblocks: &Bitvec<L, S>,
        length_bytes: &V64<L>,
    ) -> L::Assertions {
        // Assert nblocks > 0 (nblocks != 0)
        let non_zero_assertion = self
            .boolean
            .assert_false("nblocks_nz", &self.bv.is_zero(nblocks));

        // Assert nblocks <= MAX_BLOCKS
        let leq_assertion = self.boolean.assert_true(
            "nblocks_max",
            &self.bv.leq(nblocks, &self.bv.of_u64(MAX_BLOCKS as u64)),
        );

        // Zero-extend nblocks to 64 bits to prevent shift overflow
        let nblocks_64 = self.bv.zext(nblocks);

        // nblocks_times_64 = nblocks << 6
        let (nblocks_times_64, shl_assertion) = self.bv.shl_safe(6, &nblocks_64);

        // length_bytes + 9 <= nblocks * 64
        let (limit_upper, carry_upper_assertion) =
            self.bv.checked_add(length_bytes, &self.bv.of_u64(9));
        let upper_bound = self
            .boolean
            .assert_true("limit_upper", &self.bv.leq(&limit_upper, &nblocks_times_64));

        // nblocks * 64 <= length_bytes + 72
        let (limit_lower, carry_lower_assertion) =
            self.bv.checked_add(length_bytes, &self.bv.of_u64(72));
        let lower_bound = self
            .boolean
            .assert_true("limit_lower", &self.bv.leq(&nblocks_times_64, &limit_lower));

        self.logic.assert_all(
            "assert_nblocks",
            &[
                non_zero_assertion,
                leq_assertion,
                shl_assertion,
                carry_upper_assertion,
                upper_bound,
                carry_lower_assertion,
                lower_bound,
            ],
        )
    }

    /// Asserts that the actual message length matches the encoded
    /// length field embedded inside the SHA-256 padded message.
    ///
    /// Pair this with `assert_nblocks`, as in `assert_message_hash`.
    /// The comparisons are conditional and require a valid final block.
    pub fn assert_length<const S: usize>(
        &self,
        nblocks: &Bitvec<L, S>,
        length_bytes: &V64<L>,
        input_bytes: &[V8<L>],
    ) -> L::Assertions {
        let selector = self.block_selector(nblocks);
        // The encoded length field in SHA-256 padding is in bits,
        // so we must compare it to length_bytes * 8.
        let (length_bits, shl_assertion) = self.bv.shl_safe(3, length_bytes);
        let eq_assertion = self.logic.assert_mapi("len_eq", 0..MAX_BLOCKS, |b| {
            // Extract the length field from the end of block `b`.
            let encoded_len = self
                .bv
                .from_fn::<64, _>(|j| input_bytes[b * 64 + 63 - j / 8][j % 8].clone());
            self.bv
                .assert_eq_when("block_len_eq", &selector[b], &encoded_len, &length_bits)
        });
        self.logic
            .assert_all("assert_length", &[eq_assertion, shl_assertion])
    }

    /// Asserts that the message padding is correct: starts with 0x80
    /// separator, followed by zero bytes up to the length field, and
    /// that all blocks beyond the active blocks `nblocks` are
    /// completely zeroed.
    ///
    /// Pair this with `assert_nblocks`, as in `assert_message_hash`.
    /// With `length_bytes + 9 <= 64 *
    /// nblocks <= 64 * MAX_BLOCKS`, the length and the block count fit the
    /// low bits read here, and the bytes after the message other than the
    /// last block's length field are exactly those that must be zero.
    /// Each byte is checked as one packed field element, multiplied by the
    /// indicator of its required value.
    pub fn assert_sha_padding<const S: usize>(
        &self,
        nblocks: &Bitvec<L, S>,
        length_bytes: &V64<L>,
        input_bytes: &[V8<L>],
    ) -> L::Assertions {
        let arith = Arithmetic::new(self.logic);
        let block_bits = (MAX_BLOCKS.next_power_of_two().trailing_zeros() as usize).max(1);
        let length = length_bytes.as_array();
        // length = 64 * block + offset.
        let (offset, block) = (&length[..6], &length[6..6 + block_bits]);
        let block_eq: Vec<_> = (0..MAX_BLOCKS)
            .map(|q| arith.eqb(block, &arith.of_u64(block_bits, q as u64)))
            .collect();
        let offset_eq: Vec<_> = (0..64)
            .map(|r| arith.eqb(offset, &arith.of_u64(6, r as u64)))
            .collect();
        // [block < q] and [offset < r], as sums of the disjoint equalities.
        let prefix = |eq: &[Bitw<L>], n: usize| -> Vec<Eltw<L>> {
            (0..n)
                .map(|i| {
                    let below: Vec<_> = eq[..i].iter().map(|e| self.boolean.as_eltw(e)).collect();
                    self.logic.precious(&self.logic.sum(&below))
                })
                .collect()
        };
        let block_lt = prefix(&block_eq, MAX_BLOCKS);
        let offset_lt = prefix(&offset_eq, 64);
        let selector = self.block_selector(nblocks);
        let sep = self.bv.as_eltw_field(&self.bv.of_u8(0x80));

        self.logic
            .assert_mapi("byte_padding", 0..(MAX_BLOCKS * 64), |byte_idx| {
                let (q, r) = (byte_idx / 64, byte_idx % 64);
                let byte = self
                    .logic
                    .precious(&self.bv.as_eltw_field(&input_bytes[byte_idx]));
                let is_block = self.boolean.as_eltw(&block_eq[q]);
                // [length == byte_idx]
                let is_separator = self.logic.precious(
                    &self
                        .logic
                        .mul(&is_block, &self.boolean.as_eltw(&offset_eq[r])),
                );
                // [length < byte_idx]
                let mut after = vec![
                    block_lt[q].clone(),
                    self.logic.mul(&is_block, &offset_lt[r]),
                ];
                // Minus the last block's length field, which follows the
                // message.
                if r >= 56 {
                    after.push(self.logic.neg(&self.boolean.as_eltw(&selector[q])));
                }
                let is_zero = self.logic.precious(&self.logic.sum(&after));
                let not_separator = self.logic.precious(&self.logic.sub(&byte, &sep));
                self.logic.assert_all(
                    "byte_step",
                    &[
                        self.logic
                            .assert0("separator", &self.logic.mul(&is_separator, &not_separator)),
                        self.logic
                            .assert0("pad_zero", &self.logic.mul(&is_zero, &byte)),
                    ],
                )
            })
    }

    /// Verifies the full SHA-256 process of a message of byte length
    /// `length_bytes` across `nblocks` blocks, asserting that nblocks is
    /// bounds-checked and consistent with length, that the encoded padding
    /// length field matches the length in bits, and that the hash matches
    /// `expected_hash`.
    pub fn assert_message_hash<const S: usize>(
        &self,
        given: &Given<L, S>,
        derived: &Derived<V32<L>>,
    ) -> L::Assertions {
        let nblocks_assertion = self.assert_nblocks(&given.nblocks, &given.length_bytes);
        let length_assertion =
            self.assert_length(&given.nblocks, &given.length_bytes, &given.padded_preimage);

        let intermediate_hashes_assertion =
            self.assert_intermediate_hashes(&given.padded_preimage, &derived.sha_derived);
        let final_hash_assertion =
            self.assert_final_hash(&given.expected_hash, &given.nblocks, &derived.sha_derived);
        let sha_padding_assertion =
            self.assert_sha_padding(&given.nblocks, &given.length_bytes, &given.padded_preimage);

        self.logic.assert_all(
            "assert_message_hash",
            &[
                nblocks_assertion,
                length_assertion,
                intermediate_hashes_assertion,
                final_hash_assertion,
                sha_padding_assertion,
            ],
        )
    }
}
