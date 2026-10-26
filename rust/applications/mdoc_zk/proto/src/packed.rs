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

//! Canonical authenticated contract for the experimental v9 hash-input domain.
use sha2::{Digest, Sha256};
/// The Boolean variants can exceed the ordinary reader's 20M-term budget.
/// Apply this bounded override only after authenticating the explicit v9 spec.
pub const V9_MAX_TOTAL_TERMS: usize = 32_000_000;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashInputManifest {
    pub public_bits: usize,
    pub private_bits: usize,
    /// LSB-first polynomial-basis halves: digest lo/hi, pkx lo/hi, pky lo/hi.
    pub mac_starts: [usize; 6],
    pub compiler_variant: u8,
    pub witness_recipe: crate::core::bits::recipe::BitRecipe,
}
impl HashInputManifest {
    pub const HEADER_SIZE: usize = 8 + 1 + 1 + 8 * 8;
    pub fn validate(&self) -> Result<(), String> {
        if self.public_bits == 0 || self.compiler_variant > 2 {
            return Err("invalid v9 input contract".into());
        }
        self.public_bits
            .checked_add(self.private_bits)
            .ok_or("input count overflow")?;
        let semantic = self
            .private_bits
            .checked_sub(self.witness_recipe.outputs.len())
            .ok_or("invalid recipe output count")?;
        self.witness_recipe.validate(
            self.public_bits
                .checked_add(semantic)
                .ok_or("input count overflow")?,
        )?;
        if self.compiler_variant != 2
            && (!self.witness_recipe.outputs.is_empty() || !self.witness_recipe.nodes.is_empty())
        {
            return Err("unexpected witness recipe".into());
        }
        for (i, &start) in self.mac_starts.iter().enumerate() {
            let end = start.checked_add(128).ok_or("MAC bit range overflow")?;
            if end > semantic {
                return Err("MAC bit range out of bounds".into());
            }
            if self.mac_starts[..i]
                .iter()
                .any(|&x| x < end && start < x + 128)
            {
                return Err("overlapping MAC bit ranges".into());
            }
        }
        Ok(())
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = b"LFBITS01".to_vec();
        b.push(crate::core::algebra::proto::GF2_128_POLYNOMIAL_PACKING_ID);
        b.push(self.compiler_variant);
        for n in [self.public_bits, self.private_bits]
            .into_iter()
            .chain(self.mac_starts)
        {
            b.extend_from_slice(&(n as u64).to_le_bytes())
        }
        b.extend(self.witness_recipe.to_bytes());
        b
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self, String> {
        if b.len() < Self::HEADER_SIZE + 16
            || &b[..8] != b"LFBITS01"
            || b[8] != crate::core::algebra::proto::GF2_128_POLYNOMIAL_PACKING_ID
        {
            return Err("invalid hash-input manifest encoding".into());
        }
        let mut ns = [0usize; 8];
        for (n, c) in ns
            .iter_mut()
            .zip(b[10..Self::HEADER_SIZE].as_chunks::<8>().0)
        {
            *n = usize::try_from(u64::from_le_bytes(*c)).map_err(|_| "manifest count overflow")?
        }
        let result = Self {
            public_bits: ns[0],
            private_bits: ns[1],
            mac_starts: ns[2..].try_into().unwrap(),
            compiler_variant: b[9],
            witness_recipe: crate::core::bits::recipe::BitRecipe::from_bytes(
                &b[Self::HEADER_SIZE..],
            )?,
        };
        result.validate()?;
        Ok(result)
    }
    pub fn extend_witness(
        &self,
        public: &crate::core::bits::PackedBits,
        private: &mut crate::core::bits::PackedBits,
    ) -> Result<(), String> {
        self.validate()?;
        if public.len() != self.public_bits
            || private.len() + self.witness_recipe.outputs.len() != self.private_bits
        {
            return Err("semantic packed witness length mismatch".into());
        }
        let mut inputs = public.clone();
        inputs.extend(private);
        let extra = self.witness_recipe.evaluate(&inputs)?;
        private.extend(&extra);
        Ok(())
    }
    pub fn digest(&self) -> [u8; 32] {
        Sha256::digest(self.to_bytes()).into()
    }
}
