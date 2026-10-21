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

pub const K_ATTR_INDEX_BITS: usize = 10;
pub const K_DIGEST_ID: [u8; 9] = [0x68, b'd', b'i', b'g', b'e', b's', b't', b'I', b'D'];

pub const K_RANDOM_ID: [u8; 7] = [0x66, b'r', b'a', b'n', b'd', b'o', b'm'];

pub const K_ELEMENT_IDENTIFIER_PREFIX: [u8; 18] = [
    0x71, b'e', b'l', b'e', b'm', b'e', b'n', b't', b'I', b'd', b'e', b'n', b't', b'i', b'f', b'i',
    b'e', b'r',
];
pub const K_ELEMENT_VALUE_PREFIX: [u8; 13] = [
    0x6c, b'e', b'l', b'e', b'm', b'e', b'n', b't', b'V', b'a', b'l', b'u', b'e',
];

pub const K_SHA256_BLOCK_SIZE: usize = 64;
pub const K_SHA256_PADDING_LEN: usize = 9;
/// The maximum number of SHA-256 blocks for an attribute `IssuerSignedItem` in standard circuits.
/// Note: With 2 blocks (119 bytes max), attributes only support a 16-byte `random`
/// nonce in `IssuerSignedItem` when the attribute value is up to 32 bytes (e.g. `pnym_seed`).
pub const K_MAX_ATTR_SHA_BLOCKS: usize = 2;

/// The maximum number of SHA-256 blocks for a large attribute `IssuerSignedItem` (used by the
/// 2-attribute `(2, false)` circuit). Supports `IssuerSignedItemBytes` up to 247 bytes and
/// disclosed CBOR attribute values up to 192 bytes.
pub const K_LARGE_ATTR_SHA_BLOCKS: usize = 4;

/// Returns the number of SHA-256 blocks per attribute slot for a given `(num_attributes, pnym)`
/// circuit configuration. The 2-attribute non-pseudonym circuit (`(2, false)`) uses
/// `K_LARGE_ATTR_SHA_BLOCKS` (4 blocks); all other circuits use `K_MAX_ATTR_SHA_BLOCKS` (2 blocks).
#[must_use]
pub const fn attr_sha_blocks_for_circuit(num_attributes: usize, pnym: bool) -> usize {
    if num_attributes == 2 && !pnym {
        K_LARGE_ATTR_SHA_BLOCKS
    } else {
        K_MAX_ATTR_SHA_BLOCKS
    }
}

/// Minimum size (in bytes) of the `random` nonce in an `IssuerSignedItem` per ISO 18013-5.
/// Only 16-byte `random` nonces are guaranteed to fit within `K_MAX_ATTR_SHA_BLOCKS = 2`
/// for 32-byte attributes such as `pnym_seed`.
pub const K_ATTR_RANDOM_NONCE_LEN: usize = 16;

/// Returns the maximum size of the `IssuerSignedItem` CBOR structure (in bytes)
/// that fits in `num_attr_sha_blocks` SHA-256 blocks (`num_attr_sha_blocks * 64 - 9`).
#[must_use]
pub const fn max_attr_cbor_len(num_attr_sha_blocks: usize) -> usize {
    num_attr_sha_blocks * K_SHA256_BLOCK_SIZE - K_SHA256_PADDING_LEN
}

/// Returns the padded SHA-256 preimage buffer length (in bytes) for `num_attr_sha_blocks`.
#[must_use]
pub const fn attr_preimage_len(num_attr_sha_blocks: usize) -> usize {
    num_attr_sha_blocks * K_SHA256_BLOCK_SIZE
}

/// Returns the maximum disclosed CBOR attribute value buffer length (in bytes) for
/// `num_attr_sha_blocks` (`(num_attr_sha_blocks - 1) * 64`: 64 bytes for 2 blocks,
/// 192 bytes for 4 blocks).
#[must_use]
pub const fn max_attr_val_len(num_attr_sha_blocks: usize) -> usize {
    (num_attr_sha_blocks - 1) * K_SHA256_BLOCK_SIZE
}

/// Minimum CBOR overhead (in bytes) of an `IssuerSignedItemBytes` structure before the
/// CBOR-encoded `elementIdentifier` and `elementValue` fields:
/// - Outer `Tag(24)` + `bstr` header + `map(4)` header: 5 bytes (`d8 18 58 <len> a4`)
/// - `"digestID"` key (9 B) + minimum 1-byte `uint`: 10 bytes
/// - `"random"` key (7 B) + `bstr(16)` header (1 B) + 16-byte nonce: 24 bytes
/// - `"elementIdentifier"` key: 18 bytes
/// - `"elementValue"` key: 13 bytes
pub const K_MIN_ATTR_ITEM_OVERHEAD: usize = 5
    + (K_DIGEST_ID.len() + 1)
    + (K_RANDOM_ID.len() + 1 + K_ATTR_RANDOM_NONCE_LEN)
    + K_ELEMENT_IDENTIFIER_PREFIX.len()
    + K_ELEMENT_VALUE_PREFIX.len(); // 70

/// Returns the minimum encoded `IssuerSignedItemBytes` length (in bytes) for an attribute
/// whose CBOR-encoded identifier has length `cbor_id_len` and CBOR value has length `cbor_val_len`,
/// assuming a 16-byte `random` nonce.
#[must_use]
pub const fn min_attr_item_cbor_len(cbor_id_len: usize, cbor_val_len: usize) -> usize {
    K_MIN_ATTR_ITEM_OVERHEAD + cbor_id_len + cbor_val_len
}

/// The maximum size of the `IssuerSignedItem` CBOR structure that fits in the
/// standard 2-block attribute circuit (`K_MAX_ATTR_SHA_BLOCKS`).
pub const K_MAX_ATTR_CBOR_LEN: usize = max_attr_cbor_len(K_MAX_ATTR_SHA_BLOCKS); // 119
pub const K_ATTR_PREIMAGE_LEN: usize = attr_preimage_len(K_MAX_ATTR_SHA_BLOCKS); // 128
pub const K_MAX_ATTR_VAL_LEN: usize = max_attr_val_len(K_MAX_ATTR_SHA_BLOCKS); // 64

/// The maximum size of the `IssuerSignedItem` CBOR structure and buffers that fit in the
/// 4-block large attribute circuit (`K_LARGE_ATTR_SHA_BLOCKS`).
pub const K_LARGE_ATTR_CBOR_LEN: usize = max_attr_cbor_len(K_LARGE_ATTR_SHA_BLOCKS); // 247
pub const K_LARGE_ATTR_PREIMAGE_LEN: usize = attr_preimage_len(K_LARGE_ATTR_SHA_BLOCKS); // 256
pub const K_LARGE_ATTR_VAL_LEN: usize = max_attr_val_len(K_LARGE_ATTR_SHA_BLOCKS); // 192

/// Width (in bits) of the in-circuit `nblocks` wire of the attribute SHA-256 message
/// (`AttributeVerifier::assert_sha_digest_preimage`) for 2-block and 4-block attributes.
pub const K_ATTR_NBLOCKS_BITS: usize = 2;
pub const K_LARGE_ATTR_NBLOCKS_BITS: usize = 3;

// Compile-time guards for `K_MAX_ATTR_SHA_BLOCKS` and `K_LARGE_ATTR_SHA_BLOCKS`:
// every place that silently assumes the current geometry must be revisited when one of these fires.
const _: () = assert!(
    K_MAX_ATTR_SHA_BLOCKS < (1 << K_ATTR_NBLOCKS_BITS),
    "K_MAX_ATTR_SHA_BLOCKS must fit in the K_ATTR_NBLOCKS_BITS-wide nblocks wire"
);
const _: () = assert!(
    K_LARGE_ATTR_SHA_BLOCKS < (1 << K_LARGE_ATTR_NBLOCKS_BITS),
    "K_LARGE_ATTR_SHA_BLOCKS must fit in the K_LARGE_ATTR_NBLOCKS_BITS-wide nblocks wire"
);
const _: () = assert!(
    K_LARGE_ATTR_PREIMAGE_LEN < (1 << K_ATTR_INDEX_BITS),
    "attribute preimage offsets/lengths must be addressable by K_ATTR_INDEX_BITS"
);
const _: () = assert!(
    K_LARGE_ATTR_CBOR_LEN - 4 <= 0xff,
    "AttributeVerifier::assert_preimage_header assumes a 1-byte bstr length (`58 <len>`)"
);
const _: () = assert!(
    K_ELEMENT_VALUE_PREFIX.len() + K_LARGE_ATTR_VAL_LEN <= K_LARGE_ATTR_CBOR_LEN,
    "element_value_window must fit within the maximum CBOR preimage length"
);
const _: () = assert!(
    min_attr_item_cbor_len(1 + 9, 2 + 32) <= K_MAX_ATTR_CBOR_LEN,
    "a 32-byte `pnym_seed` with a 16-byte `random` nonce must fit in K_MAX_ATTR_SHA_BLOCKS"
);

// Encoding of the public 2-bit comparison operator carried by every regular attribute slot
// (`DisclosedAttribute::op`). The circuit decodes it as `bit0 = Le`, `bit1 = Ge`; the value
// `3` (both bits set) is reserved and rejected by `op_valid`. Pseudonym requests are *not*
// an operator: the pnym slot has no `op` wire (see `pnym.rs`), it is a different circuit.
// The runtime's `AttributeOp` enum uses these values as its discriminants.
pub const K_OP_BITS: usize = 2;
pub const K_OP_EQ: u8 = 0;
pub const K_OP_LE: u8 = 1;
pub const K_OP_GE: u8 = 2;

// Constants for the pseudo-nym attribute
pub const K_PNYM_SEED_LEN: usize = 32;
pub const K_PNYM_VALUE_LEN: usize = 2 + K_PNYM_SEED_LEN; // 34 (0x58, 0x20 || 32-byte digest)
pub const K_PNYM_CONTEXT_MAX: usize = 80;
pub const K_PNYM_CONTEXT_BITS: usize = 7;
pub const K_PNYM_SHA_BLOCKS: usize = 2;
pub const K_PNYM_PREIMAGE_LEN: usize = K_PNYM_SHA_BLOCKS * K_SHA256_BLOCK_SIZE; // 128
