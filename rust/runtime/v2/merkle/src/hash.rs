// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Field-independent authentication for a joint column oracle.
use sha2::{Digest as _, Sha256};

use crate::runtime::v2::proto::{Digest, MerkleNonce};
pub(in crate::runtime::v2) fn leaf(context: &Digest, j: usize, salt: &MerkleNonce) -> Sha256 {
    // Bind the layout and position as well as the values appended by the caller.
    // Independent salts hide columns whose field values have little entropy.
    let mut h = Sha256::new();
    h.update(b"polygero/joint/leaf/v1");
    h.update(context.data);
    h.update((j as u64).to_le_bytes());
    h.update(salt.bytes);
    h
}
pub(super) fn node(context: &Digest, index: usize, l: &Digest, r: &Digest) -> Digest {
    let mut h = Sha256::new();
    h.update(b"polygero/joint/node/v1");
    h.update(context.data);
    // Heap positions start at one. Binding the position keeps hash inputs at
    // different nodes distinct even when their ordered child digests coincide.
    h.update((index as u64).to_le_bytes());
    h.update(l.data);
    h.update(r.data);
    Digest {
        data: h.finalize().into(),
    }
}
