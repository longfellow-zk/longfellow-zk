// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The native witness helpers agree with each other and with SHA-256.
use sha2::{Digest, Sha256};

use crate::circuits::sha256msg::{derived, given, given_and_derived};

/// Message lengths around every padding boundary of up to three blocks.
const LENGTHS: [usize; 9] = [0, 1, 55, 56, 63, 64, 119, 120, 183];

/// The SHA-256 digest of `message` as big-endian words.
fn digest(message: &[u8]) -> [u32; 8] {
    let bytes = Sha256::digest(message);
    std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
}

/// `given`'s digest is the SHA-256 of the message, and `derived`'s last real
/// block ends in it: both hash from the standard initial state.
#[test]
fn given_digest_is_sha256_and_ends_derived() {
    for len in LENGTHS {
        let message: Vec<u8> = (0..len).map(|i| (i * 29 + len) as u8).collect();
        let g = given(&message, 3).unwrap();
        assert_eq!(g.expected_hash, digest(&message), "length {len}");
        assert_eq!(
            derived(&g, 3).sha_derived[g.nblocks - 1].h1,
            g.expected_hash,
            "length {len}"
        );
    }
}

/// `given_and_derived` computes the same given inputs and block witnesses,
/// idle blocks included, as `given` followed by `derived`, and rejects the
/// same oversized messages.
#[test]
fn given_and_derived_matches_given_then_derived() {
    for len in LENGTHS {
        let message: Vec<u8> = (0..len).map(|i| (i * 31 + len) as u8).collect();
        for max_blocks in 1..=4 {
            let separate = given(&message, max_blocks).map(|g| {
                let d = derived(&g, max_blocks);
                (g, d)
            });
            let once = given_and_derived(&message, max_blocks);
            assert_eq!(
                format!("{once:?}"),
                format!("{separate:?}"),
                "length {len}, {max_blocks} blocks"
            );
        }
    }
}
