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

//! In-circuit verifier for relying-party **pseudonyms** derived from an mdoc.
//!
//! # Scheme
//!
//! The issuer places a dedicated attribute `pnym_seed` in the credential whose value is a
//! uniformly random 32-byte string (`bstr(32)`, CBOR `58 20 || seed`). Like every other
//! attribute it is wrapped in an `IssuerSignedItem` whose SHA-256 digest is listed in the
//! MSO's `valueDigests`, and the MSO is signed by the issuer. The seed itself is never
//! disclosed.
//!
//! When a relying party (RP) asks for a pseudonym it supplies a public `context` string
//! (1..=80 raw bytes, e.g. its origin or a session identifier). The holder answers with
//!
//! ```text
//!     pnym = SHA-256( pnym_seed || context )
//! ```
//!
//! together with a zero-knowledge proof that this value was derived from the seed that the
//! issuer signed. Because `pnym_seed` has a fixed length (32 bytes) the concatenation parses
//! unambiguously, so no domain separator is needed. The same `(seed, context)` always yields
//! the same `pnym`, which lets one RP recognise a returning holder, while pseudonyms under
//! different contexts are unlinkable (modelling SHA-256 as a random oracle). Choosing and
//! authenticating `context` is the RP/wallet's responsibility; the circuit only binds whatever
//! bytes are passed in.
//!
//! # Public vs. private
//!
//! Public inputs (the verifier's statement), see [`DisclosedPnym`]:
//! * `expected_name` — CBOR text `"pnym_seed"`;
//! * `expected_cbor_value` — `58 20 || pnym` (34 bytes);
//! * `context` — RP context bytes plus their length.
//!
//! Private witness, see [`Given`]:
//! * `attribute_preimage`, `field_locator` — the `IssuerSignedItem` bytes and where its four
//!   map entries sit;
//! * `expected_digest` — SHA-256 of the item; private but *bound*, because [`crate::hash`]
//!   reads it out of the issuer-signed MSO rather than letting the prover choose it;
//! * `pnym_preimage`, `pnym_length_bytes`, `pnym_nblocks` — the padded SHA-256 message
//!   `seed || context`.
//!
//! # Statement
//!
//! [`PnymAttributeVerifier::assert_pnym_attribute`] asserts, for the private item bytes:
//!
//! 1. the item is a well-formed `#6.24(bstr IssuerSignedItem{...})` with four map entries
//!    (`digestID`, `random`, `elementIdentifier`, `elementValue`) in any order, and
//!    `SHA-256(item) == expected_digest` (all shared with [`AttributeVerifier`]);
//! 2. `elementIdentifier == expected_name` (i.e. `"pnym_seed"`);
//! 3. `elementValue` is exactly `58 20 || seed`, a 32-byte CBOR byte string;
//! 4. `1 <= context.len <= 80`, `pnym_preimage[0..32] == seed`,
//!    `pnym_preimage[32..32 + context.len] == context`, and
//!    `pnym_length_bytes == 32 + context.len`;
//! 5. `SHA-256(pnym_preimage[..pnym_length_bytes]) == pnym`, where `pnym` is read from the
//!    public `expected_cbor_value` (whose length and `58 20` header are also enforced).
//!
//! # Sizes
//!
//! `seed || context` is at most `32 + 80 = 112` bytes, so it always pads into
//! `K_PNYM_SHA_BLOCKS = 2` SHA-256 blocks (`K_PNYM_PREIMAGE_LEN = 128`). The item itself is
//! hashed with the regular attribute budget (`K_MAX_ATTR_SHA_BLOCKS = 2`, i.e. at most 119
//! bytes), which a `pnym_seed` item only meets with a 16-byte `random` nonce; see
//! `K_ATTR_RANDOM_NONCE_LEN` and `min_attr_item_cbor_len` in `constants.rs`.
//!
//! # Layout
//!
//! This module follows the crate's four-file convention in one file: the constraint logic
//! ([`PnymAttributeVerifier`]), a one-wire-per-bit allocator for circuit-level tests
//! ([`allocate_given`], [`allocate_derived`]), host-side mirrors ([`ConcreteGiven`],
//! [`ConcreteDerived`], [`derived`]) and `testonly` evaluators ([`evaluate_given`],
//! [`evaluate_derived`]). The production (bit-plucked) layout lives in
//! `compile/src/allocate_hash.rs` (`allocate_disclosed_pnym`, `allocate_pnym_wires`) and the
//! `(0 attributes + 1 pnym)` circuit is assembled by `crate::hash::MdocHash::assert_pnym`,
//! which also supplies `expected_digest` from the issuer-signed MSO.

use circuits_analog_adder::FieldWrappingSum;
use circuits_bitvec::{Bitvec, BitvecLogic, V256, V8};
use compile_logic::{Logic, LogicIO};

use super::{
    circuit::{AttrIndex, AttrSlice, AttributeVerifier, FieldLocator},
    concrete::FieldLocator as ConcreteFieldLocator,
    constants::{
        K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN, K_MAX_ATTR_SHA_BLOCKS, K_PNYM_CONTEXT_BITS,
        K_PNYM_CONTEXT_MAX, K_PNYM_PREIMAGE_LEN, K_PNYM_SEED_LEN, K_PNYM_SHA_BLOCKS,
        K_PNYM_VALUE_LEN,
    },
};

/// The public RP `context`: an 80-byte buffer plus its 7-bit length (`K_PNYM_CONTEXT_BITS`;
/// `0..=80` fits). Bytes at or beyond `len` are ignored by the circuit (they are never
/// compared or hashed).
pub type ContextSlice<L> =
    circuits_bitvec::Slice<L, V8<L>, K_PNYM_CONTEXT_MAX, K_PNYM_CONTEXT_BITS>;

/// The **public inputs** of a pseudonym request: what the verifier states it is checking.
///
/// Mirrors [`super::circuit::DisclosedAttribute`] but replaces the comparison operator with
/// the RP `context`, and fixes the value to the 34-byte pseudonym encoding.
pub struct DisclosedPnym<L: Logic> {
    /// CBOR-encoded `elementIdentifier` the item must carry (`69 "pnym_seed"`).
    pub expected_name: AttrSlice<L, 32>,
    /// The pseudonym as the RP will store it: `58 20 || SHA-256(seed || context)`.
    /// The circuit forces `len == 34` and the `58 20` header, and reads `pnym` from bytes 2..34.
    pub expected_cbor_value: AttrSlice<L, K_PNYM_VALUE_LEN>,
    /// RP-chosen context bytes; the circuit forces `1 <= len <= 80`.
    pub context: ContextSlice<L>,
}

impl<L: Logic> Clone for DisclosedPnym<L> {
    fn clone(&self) -> Self {
        Self {
            expected_name: self.expected_name.clone(),
            expected_cbor_value: self.expected_cbor_value.clone(),
            context: self.context.clone(),
        }
    }
}

/// All wires consumed by [`PnymAttributeVerifier::assert_pnym_attribute`].
///
/// Everything except `disclosed_pnym` is prover-supplied witness. `expected_digest` is
/// private too, but it is *bound*: the caller ([`crate::hash::MdocHash`]) reads it out of the
/// MSO preimage whose SHA-256 is tied to the issuer signature, so the prover cannot choose it.
pub struct Given<L: Logic> {
    /// The `IssuerSignedItem` bytes (`d8 18 58 <len> a4 ...`), zero-padded to the SHA-256
    /// buffer size, plus their true length.
    pub attribute_preimage: AttrSlice<L, K_ATTR_PREIMAGE_LEN>,
    /// Offsets/lengths of the four map entries and the permutation that maps logical slots
    /// (`digestID`, `random`, `elementIdentifier`, `elementValue`) to physical positions.
    pub field_locator: FieldLocator<L>,
    /// Public inputs, see [`DisclosedPnym`].
    pub disclosed_pnym: DisclosedPnym<L>,
    /// SHA-256 of the item as listed in the MSO's `valueDigests` (big-endian, bit 255 = MSB
    /// of the first digest byte).
    pub expected_digest: V256<L>,
    /// SHA-256-padded message `seed || context || 0x80 || 0.. || bitlen` (2 blocks).
    pub pnym_preimage: [V8<L>; K_PNYM_PREIMAGE_LEN],
    /// Unpadded length of `pnym_preimage`; forced to equal `32 + context.len`.
    pub pnym_length_bytes: AttrIndex<L>,
    /// Number of SHA-256 blocks actually used (`1` or `2`); range-checked and tied to
    /// `pnym_length_bytes` by `Sha256Msg::assert_nblocks`.
    pub pnym_nblocks: Bitvec<L, 2>,
}

/// Prover-precomputed SHA-256 round state for the two hashes the circuit *checks*
/// (rather than computes): the item hash and the pseudonym hash.
pub struct Derived<L: Logic> {
    /// Round state for `SHA-256(IssuerSignedItem)` (`K_MAX_ATTR_SHA_BLOCKS` blocks).
    pub item_sha_derived: circuits_sha256msg::Derived<L>,
    /// Round state for `SHA-256(seed || context)` (`K_PNYM_SHA_BLOCKS` blocks).
    pub pnym_sha_derived: circuits_sha256msg::Derived<L>,
}

/// Circuit gadget that proves a pseudonym was derived from an issuer-signed `pnym_seed`.
///
/// It is a thin layer over [`AttributeVerifier`]: all `IssuerSignedItem` parsing, slot
/// location and the item SHA-256 are delegated to it, and this type only adds the
/// pseudonym-specific constraints on the value slot and the second SHA-256.
pub struct PnymAttributeVerifier<'a, L: Logic>
where L::F: FieldWrappingSum
{
    /// Shared `IssuerSignedItem` machinery (CBOR header/segment checks, slot routing,
    /// byte comparison helpers and the `Sha256Msg` gadget used for *both* hashes).
    pub(crate) attr_verifier: AttributeVerifier<'a, L>,
}

impl<'a, L: Logic> PnymAttributeVerifier<'a, L>
where L::F: FieldWrappingSum
{
    /// Builds the gadget over `logic`. Cheap: it only instantiates sub-gadgets, no wires
    /// are allocated until [`Self::assert_pnym_attribute`] is called.
    pub fn new(logic: &'a L) -> Self {
        Self {
            attr_verifier: AttributeVerifier::new(logic),
        }
    }

    /// Asserts the full pseudonym statement (see the module docs) and returns the combined
    /// assertion tree rooted at `"assert_pnym_attribute"`.
    ///
    /// The checks are, in order:
    /// 1. **Item structure & digest** — `assert_item_common`: CBOR header, contiguous segment
    ///    tiling, slot permutation, `digestID` / `random` keys, `elementIdentifier ==
    ///    expected_name`, and `SHA-256(item) == expected_digest`.
    /// 2. **Value slot shape** — the `elementValue` slot is exactly `13 + 34` bytes long and
    ///    its payload starts with `58 20` (CBOR `bstr(32)`), so `got_value[2..34]` *is* the
    ///    32-byte seed.
    /// 3. **Public pseudonym shape** — `expected_cbor_value` has length 34 and the same
    ///    `58 20` header; its bytes `2..34` are reinterpreted as the 256-bit expected hash.
    /// 4. **Context bounds** — `1 <= context.len <= 80`.
    /// 5. **Message assembly** — `pnym_preimage[0..32] == seed` and
    ///    `pnym_preimage[32 + j] == context[j]` for every `j < context.len`;
    ///    `pnym_length_bytes == 32 + context.len`.
    /// 6. **Pseudonym hash** — `SHA-256(pnym_preimage[..pnym_length_bytes]) == pnym`, with
    ///    `nblocks`, padding and length-field consistency enforced by `Sha256Msg`.
    ///
    /// Nothing about the seed is revealed: it only appears in private wires and is never
    /// compared against a public value.
    pub fn assert_pnym_attribute(&self, given: &Given<L>, derived: &Derived<L>) -> L::Assertions {
        let av = &self.attr_verifier;

        // (1) Everything a regular attribute proof checks except the value relation:
        //     header, segments, permutation, digestID/random keys, elementIdentifier == name,
        //     SHA-256(item) == expected_digest.
        let [hdr, seg, perm, slot0, slot1, slot2, item_sha] = av.assert_item_common(
            &given.attribute_preimage,
            &given.field_locator,
            &given.disclosed_pnym.expected_name,
            &given.expected_digest,
            &derived.item_sha_derived,
        );

        // (2) Locate the elementValue slot and pin its payload length to 34 bytes. The
        //     window returned starts right after the `6c "elementValue"` key.
        let len_34 = av.bv.of_u64::<K_ATTR_INDEX_BITS>(K_PNYM_VALUE_LEN as u64);
        let (
            got_value,
            [overflow_assertion, key_prefix_assertion, len_eq_assertion, len_bound_assertion],
        ) = av.element_value_window(
            &given.field_locator,
            &given.attribute_preimage.data,
            &len_34,
        );

        // The signed value must be a CBOR byte string of exactly 32 bytes: `58 20 || seed`.
        let bstr32_hdr = [0x58u8, 0x20u8];
        let seed_hdr_assertion = av.assert_bytes_at(2, &got_value[0..2], &bstr32_hdr);

        // (3) The public pseudonym has the same shape: `58 20 || H`, 34 bytes.
        let value_len_assertion = av.bv.assert_eq(
            "pnym_value_len_eq",
            &given.disclosed_pnym.expected_cbor_value.len,
            &len_34,
        );
        let value_hdr_assertion = av.assert_bytes_at(
            2,
            &given.disclosed_pnym.expected_cbor_value.data[0..2],
            &bstr32_hdr,
        );

        // Reinterpret public bytes 2..34 as a 256-bit digest in the layout `Sha256Msg` uses
        // for its output: bit 255 is the MSB of the first digest byte.
        let expected_pnym_hash = av.bv.from_fn::<256, _>(|j| {
            let byte_idx = 2 + (255 - j) / 8;
            let bit_idx = j % 8;
            given.disclosed_pnym.expected_cbor_value.data[byte_idx].as_array()[bit_idx].clone()
        });

        // (4) 1 <= context.len <= K_PNYM_CONTEXT_MAX. An empty context would make the
        //     pseudonym a global identifier, so it is rejected in-circuit as well as by the
        //     runtime.
        let one_ctx = av.bv.of_u64::<K_PNYM_CONTEXT_BITS>(1);
        let max_ctx = av
            .bv
            .of_u64::<K_PNYM_CONTEXT_BITS>(K_PNYM_CONTEXT_MAX as u64);
        let ctx_ge_1 = av.bv.leq(&one_ctx, &given.disclosed_pnym.context.len);
        let ctx_le_max = av.bv.leq(&given.disclosed_pnym.context.len, &max_ctx);
        let ctx_bounds_ok = av.boolean.andb(&ctx_ge_1, &ctx_le_max);
        let ctx_bounds_assertion = av
            .boolean
            .assert_true("pnym_context_len_bounds", &ctx_bounds_ok);

        // (5a) The private SHA-256 message starts with the seed copied out of the signed
        //      item (unconditionally, all 32 bytes).
        let seed_copy_assertion = av
            .logic
            .assert_mapi("pnym_seed_copy", 0..K_PNYM_SEED_LEN, |j| {
                av.bv
                    .assert_eq("seed_byte_eq", &given.pnym_preimage[j], &got_value[2 + j])
            });

        // (5b) ... followed by the public context, byte for byte, for j < context.len.
        //      Bytes past the context length are left to `Sha256Msg::assert_sha_padding`,
        //      which forces them to be the 0x80 / zero / bit-length padding.
        let ctx_copy_assertion =
            av.logic
                .assert_mapi("pnym_context_copy", 0..K_PNYM_CONTEXT_MAX, |j| {
                    let j_wire = av.bv.of_u64::<K_PNYM_CONTEXT_BITS>(j as u64);
                    let in_bounds = av.bv.lt(&j_wire, &given.disclosed_pnym.context.len);
                    let eq_bit = av.bv.eqb(
                        &given.pnym_preimage[K_PNYM_SEED_LEN + j],
                        &given.disclosed_pnym.context.data[j],
                    );
                    let imp = av.boolean.impliesb(&in_bounds, &eq_bit);
                    av.boolean.assert_true("ctx_byte_imp", &imp)
                });

        // (5c) The hashed length is exactly 32 + context.len, so the prover can neither drop
        //      context bytes nor append extra ones.
        let seed_len_10 = av.bv.of_u64::<K_ATTR_INDEX_BITS>(K_PNYM_SEED_LEN as u64);
        let ctx_len_10 = av
            .bv
            .zext::<K_PNYM_CONTEXT_BITS, K_ATTR_INDEX_BITS>(&given.disclosed_pnym.context.len);
        let pnym_len_assertion =
            av.bv
                .assert_checked_add(&given.pnym_length_bytes, &seed_len_10, &ctx_len_10);

        // (6) SHA-256(seed || context) == H. `Sha256Msg` additionally range-checks
        //     `pnym_nblocks` against the length, verifies the padding bytes and checks the
        //     prover-supplied round state in `derived.pnym_sha_derived`.
        let pnym_len_64 = av
            .bv
            .zext::<K_ATTR_INDEX_BITS, 64>(&given.pnym_length_bytes);
        let pnym_sha_given = circuits_sha256msg::circuit::Given {
            padded_preimage: given.pnym_preimage.to_vec(),
            nblocks: given.pnym_nblocks.clone(),
            length_bytes: pnym_len_64,
            expected_hash: expected_pnym_hash,
        };
        let pnym_sha_assertion = av
            .shamsg
            .assert_message_hash(&pnym_sha_given, &derived.pnym_sha_derived);

        // Everything concerning the value slot and the pseudonym hash takes the place of
        // the `slot3` assertion of a regular attribute.
        let slot3_and_pnym = av.logic.assert_all(
            "assert_pnym_value_and_hash",
            &[
                overflow_assertion,
                key_prefix_assertion,
                len_eq_assertion,
                len_bound_assertion,
                seed_hdr_assertion,
                value_len_assertion,
                value_hdr_assertion,
                ctx_bounds_assertion,
                seed_copy_assertion,
                ctx_copy_assertion,
                pnym_len_assertion,
                pnym_sha_assertion,
            ],
        );

        // Same shape as `AttributeVerifier::assert_attribute` so the assertion paths line up
        // in debug symbols and corruptor tests.
        av.logic.assert_all(
            "assert_pnym_attribute",
            &[
                hdr,
                seg,
                perm,
                slot0,
                slot1,
                slot2,
                slot3_and_pnym,
                item_sha,
            ],
        )
    }
}

/// Allocates one input wire per bit for every field of [`Given`], advancing `pos`.
///
/// This is the *test* layout used by the circuit-level `EvalLogic`/`compile_eval` tests
/// (the order here must match [`evaluate_given`]). The production circuit packs several
/// bits per field element and allocates public inputs first; see
/// `compile/src/allocate_hash.rs`.
pub fn allocate_given<L: LogicIO>(bv: &BitvecLogic<L>, pos: &mut usize) -> Given<L> {
    let bitvec_io = circuits_bitvec::BitvecIO::new(bv);
    let attribute_preimage = AttrSlice {
        data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
        len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
    };
    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
        length: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
        permutation: std::array::from_fn(|_| bitvec_io.next::<2>(pos)),
    };
    let disclosed_pnym = DisclosedPnym {
        expected_name: AttrSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        },
        expected_cbor_value: AttrSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        },
        context: ContextSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_PNYM_CONTEXT_BITS>(pos),
        },
    };
    let expected_digest = bitvec_io.next::<256>(pos);
    let pnym_preimage = std::array::from_fn(|_| bitvec_io.next::<8>(pos));
    let pnym_length_bytes = bitvec_io.next::<K_ATTR_INDEX_BITS>(pos);
    let pnym_nblocks = bitvec_io.next::<2>(pos);

    Given {
        attribute_preimage,
        field_locator,
        disclosed_pnym,
        expected_digest,
        pnym_preimage,
        pnym_length_bytes,
        pnym_nblocks,
    }
}

/// Allocates the SHA-256 round-state witness wires for both hashes (item first, then
/// pseudonym), advancing `pos`. Test layout; counterpart of [`evaluate_derived`].
pub fn allocate_derived<L: LogicIO>(bv: &BitvecLogic<L>, pos: &mut usize) -> Derived<L> {
    Derived {
        item_sha_derived: circuits_sha256msg::allocate_derived::<_, K_MAX_ATTR_SHA_BLOCKS>(bv, pos),
        pnym_sha_derived: circuits_sha256msg::allocate_derived::<_, K_PNYM_SHA_BLOCKS>(bv, pos),
    }
}

/// Host-side (plain Rust) mirror of [`Given`], as produced from a parsed mdoc plus the RP
/// context. `preimage` is the *unpadded* item; the SHA-256 padding for it is recomputed in
/// [`derived`] / [`evaluate_given`], whereas the pseudonym message is stored already padded.
#[derive(Clone, Debug)]
pub struct ConcreteGiven {
    /// CBOR-encoded `elementIdentifier` (`69 "pnym_seed"`).
    pub name: Vec<u8>,
    /// `58 20 || SHA-256(seed || context)` (34 bytes).
    pub cbor_value: Vec<u8>,
    /// RP context, 1..=80 raw bytes.
    pub context: Vec<u8>,
    /// Unpadded `IssuerSignedItem` bytes (`d8 18 58 <len> a4 ...`), at most
    /// `max_attr_cbor_len(K_MAX_ATTR_SHA_BLOCKS)` bytes.
    pub preimage: Vec<u8>,
    /// Slot offsets/lengths and packed permutation (2 bits per logical slot).
    pub field_locator: ConcreteFieldLocator,
    /// `SHA-256(preimage)` as eight big-endian words (the MSO `valueDigests` entry).
    pub expected_digest: [u32; 8],
    /// `seed || context`, SHA-256 padded to `K_PNYM_PREIMAGE_LEN` bytes.
    pub pnym_padded_preimage: Vec<u8>,
    /// `32 + context.len()`.
    pub pnym_length_bytes: usize,
    /// Number of SHA-256 blocks the padded pseudonym message occupies (1 or 2).
    pub pnym_nblocks: usize,
}

/// Host-side mirror of [`Derived`].
#[derive(Clone, Debug)]
pub struct ConcreteDerived {
    pub item_sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
    pub pnym_sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
}

/// Computes the prover-side SHA-256 round state for both hashes from a [`ConcreteGiven`].
///
/// # Panics
/// If `given.preimage` does not fit in `K_MAX_ATTR_SHA_BLOCKS` blocks. Callers (tests and the
/// runtime witness builders) are expected to have rejected such items already with
/// `AttributeTooLong`.
#[must_use]
pub fn derived(given: &ConcreteGiven) -> ConcreteDerived {
    let (_, _, padded_preimage) =
        circuits_sha256msg::concrete::pad_sha256_message(&given.preimage, K_MAX_ATTR_SHA_BLOCKS)
            .unwrap();
    ConcreteDerived {
        item_sha_derived: circuits_sha256msg::concrete::ConcreteDerived {
            sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
                &padded_preimage,
                &circuits_sha256::constants::INITIAL,
                K_MAX_ATTR_SHA_BLOCKS,
            ),
        },
        pnym_sha_derived: circuits_sha256msg::concrete::ConcreteDerived {
            sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
                &given.pnym_padded_preimage,
                &circuits_sha256::constants::INITIAL,
                K_PNYM_SHA_BLOCKS,
            ),
        },
    }
}

/// Lifts a [`ConcreteGiven`] into constant wires so [`PnymAttributeVerifier`] can be run
/// directly under `EvalLogic` in tests. Field order and encodings match [`allocate_given`];
/// buffers shorter than their wire arrays are zero-padded.
#[cfg(feature = "testonly")]
pub fn evaluate_given<L: Logic>(given: &ConcreteGiven, bv: &BitvecLogic<L>) -> Given<L> {
    let get_padded = |vec: &[u8], i: usize| -> u8 { vec.get(i).copied().unwrap_or(0) };
    let (_, _, padded_preimage) =
        circuits_sha256msg::concrete::pad_sha256_message(&given.preimage, K_MAX_ATTR_SHA_BLOCKS)
            .unwrap();

    let attribute_preimage = AttrSlice {
        data: std::array::from_fn(|i| bv.of_u8(get_padded(&padded_preimage, i))),
        len: bv.of_u64::<K_ATTR_INDEX_BITS>(given.preimage.len() as u64),
    };
    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|i| {
            bv.of_u64::<K_ATTR_INDEX_BITS>(given.field_locator.slot_position[i] as u64)
        }),
        length: std::array::from_fn(|i| {
            bv.of_u64::<K_ATTR_INDEX_BITS>(given.field_locator.length[i] as u64)
        }),
        permutation: std::array::from_fn(|i| {
            let slot = (given.field_locator.permutation >> (2 * i)) & 3;
            bv.of_u64::<2>(slot as u64)
        }),
    };
    let disclosed_pnym = DisclosedPnym {
        expected_name: AttrSlice {
            data: std::array::from_fn(|i| bv.of_u8(get_padded(&given.name, i))),
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(given.name.len() as u64),
        },
        expected_cbor_value: AttrSlice {
            data: std::array::from_fn(|i| bv.of_u8(get_padded(&given.cbor_value, i))),
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(given.cbor_value.len() as u64),
        },
        context: ContextSlice {
            data: std::array::from_fn(|i| bv.of_u8(get_padded(&given.context, i))),
            len: bv.of_u64::<K_PNYM_CONTEXT_BITS>(given.context.len() as u64),
        },
    };
    let boolean = circuits_boolean::Boolean::new(bv.logic());
    // Same bit layout as `expected_pnym_hash` in `assert_pnym_attribute`: V256 bit 255 is the
    // MSB of digest word 0 (i.e. of the first digest byte), bit 0 the LSB of word 7.
    let expected_digest = bv.from_fn::<256, _>(|idx| {
        let word_idx = 7 - (idx / 32);
        let bit_idx = idx % 32;
        let w = given.expected_digest[word_idx];
        let bit_val = (w.checked_shr(bit_idx as u32).unwrap_or(0) & 1) == 1;
        boolean.konst(bit_val)
    });
    let pnym_preimage =
        std::array::from_fn(|i| bv.of_u8(get_padded(&given.pnym_padded_preimage, i)));
    let pnym_length_bytes = bv.of_u64::<K_ATTR_INDEX_BITS>(given.pnym_length_bytes as u64);
    let pnym_nblocks = bv.of_u64::<2>(given.pnym_nblocks as u64);

    Given {
        attribute_preimage,
        field_locator,
        disclosed_pnym,
        expected_digest,
        pnym_preimage,
        pnym_length_bytes,
        pnym_nblocks,
    }
}

/// Lifts a [`ConcreteDerived`] into constant wires (test counterpart of
/// [`allocate_derived`]); order is item hash first, then pseudonym hash.
#[cfg(feature = "testonly")]
pub fn evaluate_derived<L: Logic>(derived: &ConcreteDerived, bv: &BitvecLogic<L>) -> Derived<L> {
    Derived {
        item_sha_derived: circuits_sha256msg::evaluate::evaluate_derived(
            &derived.item_sha_derived,
            bv,
        ),
        pnym_sha_derived: circuits_sha256msg::evaluate::evaluate_derived(
            &derived.pnym_sha_derived,
            bv,
        ),
    }
}
