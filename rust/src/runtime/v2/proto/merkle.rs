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

//! V2 Merkle proof messages and their wire encoding.

cfg_role! {
    mod codec;
}
cfg_prover! {
    mod prover;
}

/// Bytes per digest: a root, a frontier node or a leaf hash.
pub(super) const DIGEST_LEN: usize = 32;
/// Salt bytes per v2 column, shared by commitment sampling and the proof codec.
/// Independent 256-bit salts give indexed-leaf statistical hiding error at
/// most (Qpre + Qpost)/2^256 in the ideal-oracle model.
pub const NONCE_LEN: usize = 32;

/// A 32-byte cryptographic hash digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Digest {
    pub data: [u8; DIGEST_LEN],
}

/// A salt value generated randomly per leaf/column to make the
/// commitment zero-knowledge (hiding). An unopened nonce is secret, so its
/// `Debug` output omits the bytes.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::runtime::v2) struct MerkleNonce {
    pub(in crate::runtime::v2) bytes: [u8; NONCE_LEN],
}
impl std::fmt::Debug for MerkleNonce {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleNonce").finish_non_exhaustive()
    }
}

/// A Merkle proof of opening for a subset of leaves.
/// It contains:
/// - `nonce`: The nonces corresponding to the opened leaves, allowing the verifier to reconstruct
///   the leaf hashes.
/// - `path`: Sibling digests along the paths from the opened leaves to the root.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::runtime::v2) struct MerkleProof {
    pub(in crate::runtime::v2) nonce: Vec<MerkleNonce>,
    pub(in crate::runtime::v2) path: Vec<Digest>,
}
