// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A page-Merkle SHA-256 commitment to canonical circuit bytes.
//!
//! This is intentionally independent of [`crate::circuit::compute_id`].  The
//! latter expands every circuit term and is prohibitively expensive to replay
//! in a proof assistant for large circuits.  This commitment instead pins the
//! exact compact byte representation that the verified decoder consumes.
//!
//! All integer fields are fixed-width little-endian.  Domain tags include a
//! trailing NUL byte, so none is a prefix of another protocol input.  An odd
//! node is paired with itself.  The root envelope commits to both the byte
//! length and leaf count, making that padding rule unambiguous.

use sha2::{Digest, Sha256};

use crate::circuit::DigestBytes;

/// Page size chosen to keep generated Lean constants and individual SHA
/// checks small enough to elaborate independently.
pub const FORMAL_PAGE_SIZE: usize = 4096;

const LEAF_DOMAIN: &[u8] = b"LFZK-LFC-PAGE-V1\0";
const NODE_DOMAIN: &[u8] = b"LFZK-LFC-NODE-V1\0";
const ROOT_DOMAIN: &[u8] = b"LFZK-LFC-ROOT-V1\0";

/// Metadata accompanying a formal circuit commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormalCircuitCommitment {
    pub root: DigestBytes,
    pub byte_len: u64,
    pub page_count: u64,
}

impl FormalCircuitCommitment {
    /// Computes the protocol commitment for an exact byte string.
    #[must_use]
    pub fn new(bytes: &[u8]) -> Self {
        let byte_len = u64::try_from(bytes.len()).expect("circuit payload length exceeds u64");
        let page_count_usize = bytes.len().div_ceil(FORMAL_PAGE_SIZE).max(1);
        let page_count = u64::try_from(page_count_usize).expect("circuit page count exceeds u64");

        let mut level: Vec<DigestBytes> = if bytes.is_empty() {
            vec![formal_page_leaf_hash(byte_len, 0, &[])]
        } else {
            bytes
                .chunks(FORMAL_PAGE_SIZE)
                .enumerate()
                .map(|(index, page)| {
                    formal_page_leaf_hash(
                        byte_len,
                        u64::try_from(index).expect("circuit page index exceeds u64"),
                        page,
                    )
                })
                .collect()
        };

        let mut tree_level = 0u32;
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len().div_ceil(2));
            for pair in level.chunks(2) {
                let right = pair.get(1).unwrap_or(&pair[0]);
                next.push(hash_node(tree_level, &pair[0], right));
            }
            level = next;
            tree_level = tree_level
                .checked_add(1)
                .expect("circuit commitment tree depth exceeds u32");
        }

        let root = hash_root(byte_len, page_count, &level[0]);
        Self {
            root,
            byte_len,
            page_count,
        }
    }

    /// Checks both the committed metadata and root.
    #[must_use]
    pub fn verifies(&self, bytes: &[u8]) -> bool {
        *self == Self::new(bytes)
    }
}

/// Verifies the single 32-byte value that a circuit verifier needs to pin.
/// Length and page count need not be stored separately: the root envelope
/// commits to both values derived from `bytes`.
#[must_use]
pub fn verifies_formal_circuit_root(bytes: &[u8], expected_root: &DigestBytes) -> bool {
    FormalCircuitCommitment::new(bytes).root == *expected_root
}

#[must_use]
pub fn formal_page_leaf_hash(byte_len: u64, page_index: u64, page: &[u8]) -> DigestBytes {
    let page_len = u32::try_from(page.len()).expect("formal circuit page exceeds u32");
    debug_assert!(page.len() <= FORMAL_PAGE_SIZE);

    let mut hasher = Sha256::new();
    hasher.update(LEAF_DOMAIN);
    hasher.update(byte_len.to_le_bytes());
    hasher.update(page_index.to_le_bytes());
    hasher.update(page_len.to_le_bytes());
    hasher.update(page);
    hasher.finalize().into()
}

#[must_use]
fn hash_node(tree_level: u32, left: &DigestBytes, right: &DigestBytes) -> DigestBytes {
    let mut hasher = Sha256::new();
    hasher.update(NODE_DOMAIN);
    hasher.update(tree_level.to_le_bytes());
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

#[must_use]
fn hash_root(byte_len: u64, page_count: u64, tree_root: &DigestBytes) -> DigestBytes {
    let mut hasher = Sha256::new();
    hasher.update(ROOT_DOMAIN);
    hasher.update(
        u32::try_from(FORMAL_PAGE_SIZE)
            .expect("formal page size exceeds u32")
            .to_le_bytes(),
    );
    hasher.update(byte_len.to_le_bytes());
    hasher.update(page_count.to_le_bytes());
    hasher.update(tree_root);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commitment_covers_empty_and_page_boundaries() {
        for len in [
            0,
            1,
            FORMAL_PAGE_SIZE - 1,
            FORMAL_PAGE_SIZE,
            FORMAL_PAGE_SIZE + 1,
        ] {
            let bytes: Vec<u8> = (0..len).map(|i| i as u8).collect();
            let commitment = FormalCircuitCommitment::new(&bytes);
            assert_eq!(commitment.byte_len, len as u64);
            assert_eq!(
                commitment.page_count,
                len.div_ceil(FORMAL_PAGE_SIZE).max(1) as u64
            );
            assert!(commitment.verifies(&bytes));
        }
    }

    #[test]
    fn commitment_detects_content_length_order_and_metadata_changes() {
        let bytes: Vec<u8> = (0..FORMAL_PAGE_SIZE + 17)
            .map(|i| (i * 37 + i / FORMAL_PAGE_SIZE) as u8)
            .collect();
        let commitment = FormalCircuitCommitment::new(&bytes);

        let mut changed = bytes.clone();
        changed[FORMAL_PAGE_SIZE] ^= 1;
        assert!(!commitment.verifies(&changed));

        changed = bytes.clone();
        changed.swap(0, FORMAL_PAGE_SIZE);
        assert!(!commitment.verifies(&changed));

        assert!(!commitment.verifies(&bytes[..bytes.len() - 1]));

        let mut wrong_metadata = commitment;
        wrong_metadata.page_count += 1;
        assert!(!wrong_metadata.verifies(&bytes));
    }

    #[test]
    fn protocol_roots_match_formal_test_vectors() {
        assert_eq!(
            FormalCircuitCommitment::new(&[]).root,
            [
                0x66, 0x62, 0xec, 0x67, 0xad, 0x66, 0x72, 0xb6, 0x05, 0xc1, 0xe6, 0x56, 0x31, 0x2a,
                0xb3, 0xc9, 0x36, 0xd3, 0xef, 0x73, 0x42, 0xcd, 0x05, 0x71, 0xaf, 0x80, 0xa2, 0x76,
                0x48, 0xc1, 0xaa, 0x37,
            ]
        );
        assert_eq!(
            FormalCircuitCommitment::new(b"abc").root,
            [
                0x18, 0x7a, 0xb7, 0xe2, 0x47, 0x37, 0x1c, 0x59, 0x4f, 0xfe, 0x6f, 0xbf, 0x4d, 0xf6,
                0xc6, 0xa5, 0x6d, 0xef, 0xbd, 0x29, 0x3c, 0x43, 0xac, 0x65, 0xfe, 0x86, 0xc7, 0x03,
                0xca, 0x9a, 0xb9, 0xe0,
            ]
        );

        let leaves: Vec<DigestBytes> = (0u8..3)
            .map(|page| {
                let start = page * 32;
                std::array::from_fn(|offset| start + offset as u8)
            })
            .collect();
        let first = hash_node(0, &leaves[0], &leaves[1]);
        let second = hash_node(0, &leaves[2], &leaves[2]);
        let tree_root = hash_node(1, &first, &second);
        assert_eq!(
            hash_root(9000, 3, &tree_root),
            [
                0x21, 0x55, 0x06, 0x1e, 0x5f, 0xd2, 0x9d, 0x7a, 0xb4, 0x14, 0xcf, 0x38, 0xa0, 0x8f,
                0xbb, 0x97, 0xfc, 0xe1, 0xb5, 0xc5, 0x90, 0x96, 0xd6, 0xe7, 0xd1, 0x16, 0x3c, 0x50,
                0x22, 0x95, 0xea, 0xeb,
            ]
        );
    }
}
