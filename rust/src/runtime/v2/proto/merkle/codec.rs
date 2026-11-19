// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The decoding of a Merkle opening, which every proof role runs.
use super::{super::read_bytes_32, Digest, MerkleNonce, MerkleProof, DIGEST_LEN, NONCE_LEN};

impl MerkleProof {
    /// Reads `num_queries` nonces from the byte buffer.
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

    /// Reads the frontier: its u64 count, at most `max_sz` (the opening's
    /// checked frontier capacity), then that many digests. Bytes after them
    /// are left to the caller.
    pub(in crate::runtime::v2) fn read_path(
        bytes: &mut &[u8],
        max_sz: usize,
    ) -> Result<Vec<Digest>, std::io::Error> {
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
