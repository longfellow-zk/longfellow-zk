// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! NEXT's authenticated Boolean-input domain.
use sha2::{Digest, Sha256};
pub const V9_MAX_TOTAL_TERMS: usize = 32_000_000;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HashInputManifest {
    pub public_bits: usize,
    pub private_bits: usize,
}
impl HashInputManifest {
    pub const HEADER_SIZE: usize = 24;
    pub fn validate(&self) -> Result<(), String> {
        if self.public_bits == 0 {
            return Err("invalid NEXT input contract".into());
        }
        self.public_bits
            .checked_add(self.private_bits)
            .ok_or("input count overflow")?;
        Ok(())
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = b"LFHASH03".to_vec();
        for n in [self.public_bits, self.private_bits] {
            b.extend_from_slice(&(n as u64).to_le_bytes())
        }
        b
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self, String> {
        if b.len() != Self::HEADER_SIZE || &b[..8] != b"LFHASH03" {
            return Err("invalid hash-input manifest".into());
        }
        let counts = b[8..].as_chunks::<8>().0;
        let result = Self {
            public_bits: usize::try_from(u64::from_le_bytes(counts[0]))
                .map_err(|_| "manifest count overflow")?,
            private_bits: usize::try_from(u64::from_le_bytes(counts[1]))
                .map_err(|_| "manifest count overflow")?,
        };
        result.validate()?;
        Ok(result)
    }
    pub fn validate_witness(
        &self,
        public: &[crate::runtime::algebra::gf2_128::Gf2_128],
        private: &[crate::runtime::algebra::gf2_128::Gf2_128],
    ) -> Result<(), String> {
        self.validate()?;
        if public.len() != self.public_bits || private.len() != self.private_bits {
            return Err("witness length mismatch".into());
        }
        if public.iter().chain(private).any(|v| v.to_u128() > 1) {
            return Err("nonboolean witness".into());
        }
        Ok(())
    }
    pub fn digest(&self) -> [u8; 32] {
        Sha256::digest(self.to_bytes()).into()
    }
}
