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
/// Bytes of a disclosed attribute's CBOR identifier slot.
pub const K_ATTR_ID_BYTES: usize = 32;
/// CBOR operand buffer width of an equality slot. The signed item's
/// identifier, nonce and framing also count toward the item size limit.
pub const K_ATTR_VALUE_BYTES: usize = 192;
/// Public relation flags, in order: less-than-or-equal, greater-than-or-equal.
/// Neither flag selects exact equality. Both flags set is invalid.
pub const K_ATTR_COMPARISON_BITS: usize = 2;

pub const K_DATE_SLOT: usize = super::super::config::NEXT_ATTRIBUTES - 1;
pub const K_DATE_VALUE_BYTES: usize = 22;

/// Width of a slot's public CBOR operand buffer.
pub const fn attr_value_bytes(slot: usize) -> usize {
    if slot == K_DATE_SLOT {
        K_DATE_VALUE_BYTES
    } else {
        K_ATTR_VALUE_BYTES
    }
}

/// The canonical CBOR headers and encoded lengths of the two ordered date types.
pub const K_ORDERED_DATE_ENCODINGS: [(&[u8], usize); 2] = [
    (&[0xd9, 0x03, 0xec, 0x6a], 14),
    (&[0xc0, 0x74], K_DATE_VALUE_BYTES),
];

/// Whether the bytes have one of the two fixed-width ordered date encodings.
pub fn has_ordered_date_encoding(bytes: &[u8]) -> bool {
    K_ORDERED_DATE_ENCODINGS
        .iter()
        .any(|&(prefix, len)| bytes.len() == len && bytes.starts_with(prefix))
}
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
/// The SHA-256 block budget of each equality slot and the date slot.
pub const K_MAX_ATTR_SHA_BLOCKS: usize = 4;
pub const K_DATE_ATTR_SHA_BLOCKS: usize = 2;
pub const K_DATE_ATTR_PREIMAGE_LEN: usize = K_DATE_ATTR_SHA_BLOCKS * K_SHA256_BLOCK_SIZE;
pub const K_DATE_MAX_ATTR_CBOR_LEN: usize = K_DATE_ATTR_PREIMAGE_LEN - K_SHA256_PADDING_LEN;
pub const K_ATTR_PREIMAGE_LEN: usize = K_MAX_ATTR_SHA_BLOCKS * K_SHA256_BLOCK_SIZE;
/// The largest complete SHA-256 preimage before padding.
pub const K_MAX_ATTR_CBOR_LEN: usize = K_ATTR_PREIMAGE_LEN - K_SHA256_PADDING_LEN;

pub const fn attr_sha_blocks(slot: usize) -> usize {
    if slot == K_DATE_SLOT {
        K_DATE_ATTR_SHA_BLOCKS
    } else {
        K_MAX_ATTR_SHA_BLOCKS
    }
}
