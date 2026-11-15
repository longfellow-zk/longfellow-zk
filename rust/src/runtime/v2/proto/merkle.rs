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

#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::v2::proto::util::read_bytes_32;

const DIGEST_LEN: usize = 32;
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
/// commitment zero-knowledge (hiding).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::runtime::v2) struct MerkleNonce {
    pub(in crate::runtime::v2) bytes: [u8; NONCE_LEN],
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

impl MerkleProof {
    /// Writes the nonces to a byte buffer (raw bytes of each nonce, no length
    /// prefix).
    pub(in crate::runtime::v2) fn write_nonces(&self, buf: &mut Vec<u8>) {
        for n in &self.nonce {
            buf.extend_from_slice(&n.bytes);
        }
    }

    /// Reads `num_queries` nonces from the byte buffer.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(in crate::runtime::v2) fn read_nonces(
        bytes: &mut &[u8],
        num_queries: usize,
    ) -> Result<Vec<MerkleNonce>, std::io::Error> {
        use std::io::{Error, ErrorKind, Read};

        if num_queries > bytes.len() / NONCE_LEN {
            return Err(Error::new(
                ErrorKind::UnexpectedEof,
                "Truncated Merkle nonces",
            ));
        }
        let mut nonce = Vec::with_capacity(num_queries);
        for _ in 0..num_queries {
            let mut n_bytes = [0; NONCE_LEN];
            bytes.read_exact(&mut n_bytes)?;
            nonce.push(MerkleNonce { bytes: n_bytes });
        }
        Ok(nonce)
    }

    /// Writes the frontier: a u64 little-endian count of digests, then the
    /// raw digests.
    pub(in crate::runtime::v2) fn write_path(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&(self.path.len() as u64).to_le_bytes());
        for d in &self.path {
            buf.extend_from_slice(&d.data);
        }
    }

    /// Reads the frontier: its u64 count, at most `num_queries * mc_pathlen`,
    /// then that many digests. Bytes after them are left to the caller.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(in crate::runtime::v2) fn read_path(
        bytes: &mut &[u8],
        num_queries: usize,
        mc_pathlen: usize,
    ) -> Result<Vec<Digest>, std::io::Error> {
        let max_sz = num_queries.checked_mul(mc_pathlen).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Overflow computing max Merkle path size",
            )
        })?;
        let invalid = || {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Invalid Merkle frontier count (max {max_sz} digests)"),
            )
        };
        let (word, rest) = bytes.split_first_chunk::<8>().ok_or_else(invalid)?;
        let count = usize::try_from(u64::from_le_bytes(*word)).map_err(|_| invalid())?;
        if count > max_sz
            || count
                .checked_mul(DIGEST_LEN)
                .is_none_or(|len| len > rest.len())
        {
            return Err(invalid());
        }
        *bytes = rest;
        let mut path = Vec::with_capacity(count);
        for _ in 0..count {
            path.push(Digest {
                data: read_bytes_32(bytes)?,
            });
        }
        Ok(path)
    }
}
