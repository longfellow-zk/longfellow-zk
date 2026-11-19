// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's encoding of a Merkle opening.
use super::MerkleProof;

impl MerkleProof {
    /// Writes the nonces to a byte buffer (raw bytes of each nonce, no length
    /// prefix).
    pub(in crate::runtime::v2) fn write_nonces(&self, buf: &mut Vec<u8>) {
        for n in &self.nonce {
            buf.extend_from_slice(&n.bytes);
        }
    }

    /// Writes the frontier: a u64 little-endian count of digests, then the
    /// raw digests.
    pub(in crate::runtime::v2) fn write_path(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&(self.path.len() as u64).to_le_bytes());
        for d in &self.path {
            buf.extend_from_slice(&d.data);
        }
    }
}
