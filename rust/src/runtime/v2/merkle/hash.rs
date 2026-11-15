// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Field-independent authentication for a joint column oracle.
//!
//! Every leaf and node hash input starts with its role label, then the
//! Merkle hash domain `DOMAIN`, then its position. The two role labels have
//! equal length and differ, so no leaf input equals a node input, and both
//! differ from every transcript hash input, which starts with a u32 strand or
//! PRF kind. The domain is a protocol constant: the parameters that fix the
//! tree's shape and the leaf layout are bound by the transcript statement,
//! and the evaluation-domain ID is bound nowhere, since the verifier fixes it.
use sha2::{Digest as _, Sha256};

use crate::runtime::v2::proto::{Digest, MerkleNonce};

/// The Merkle hash domain of v2 commitments: the label
/// `longfellow/v2/merkle/domain`, zero-padded to 32 bytes.
pub(super) const DOMAIN: [u8; 32] = *b"longfellow/v2/merkle/domain\0\0\0\0\0";

pub(in crate::runtime::v2) fn leaf(j: usize, salt: &MerkleNonce) -> Sha256 {
    // Bind the position as well as the values appended by the caller.
    // Independent salts hide columns whose field values have little entropy.
    let mut h = Sha256::new();
    h.update(b"polygero/joint/leaf/v1");
    h.update(DOMAIN);
    h.update((j as u64).to_le_bytes());
    h.update(salt.bytes);
    h
}
pub(super) fn node(index: usize, l: &Digest, r: &Digest) -> Digest {
    let mut h = Sha256::new();
    h.update(b"polygero/joint/node/v1");
    h.update(DOMAIN);
    // Heap positions start at one. Binding the position keeps hash inputs at
    // different nodes distinct even when their ordered child digests coincide.
    h.update((index as u64).to_le_bytes());
    h.update(l.data);
    h.update(r.data);
    Digest {
        data: h.finalize().into(),
    }
}
