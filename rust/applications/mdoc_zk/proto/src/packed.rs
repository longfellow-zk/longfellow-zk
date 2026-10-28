// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Semantic Boolean witness recipe; independent of commitment packing.
use sha2::{Digest, Sha256};
pub const V9_MAX_TOTAL_TERMS: usize = 32_000_000;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashInputManifest {
    pub public_bits: usize,
    pub private_bits: usize,
    pub compiler_variant: u8,
    pub witness_recipe: crate::core::bits::recipe::BitRecipe,
}
impl HashInputManifest {
    pub const HEADER_SIZE: usize = 25;
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
            && (!self.witness_recipe.nodes.is_empty() || !self.witness_recipe.outputs.is_empty())
        {
            return Err("unexpected witness recipe".into());
        }
        Ok(())
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = b"LFHASH02".to_vec();
        b.push(self.compiler_variant);
        for n in [self.public_bits, self.private_bits] {
            b.extend_from_slice(&(n as u64).to_le_bytes());
        }
        b.extend(self.witness_recipe.to_bytes());
        b
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self, String> {
        if b.len() < Self::HEADER_SIZE + 16 || &b[..8] != b"LFHASH02" {
            return Err("invalid hash-input manifest".into());
        }
        let mut counts = [0; 2];
        for (n, c) in counts.iter_mut().zip(b[9..25].as_chunks::<8>().0) {
            *n = usize::try_from(u64::from_le_bytes(*c)).map_err(|_| "manifest count overflow")?;
        }
        let result = Self {
            public_bits: counts[0],
            private_bits: counts[1],
            compiler_variant: b[8],
            witness_recipe: crate::core::bits::recipe::BitRecipe::from_bytes(&b[25..])?,
        };
        result.validate()?;
        Ok(result)
    }
    pub fn extend_witness(
        &self,
        public: &[crate::runtime::algebra::gf2_128::Gf2_128],
        private: &mut Vec<crate::runtime::algebra::gf2_128::Gf2_128>,
    ) -> Result<(), String> {
        self.validate()?;
        if public.len() != self.public_bits
            || private.len() + self.witness_recipe.outputs.len() != self.private_bits
        {
            return Err("semantic witness length mismatch".into());
        }
        let inputs = public
            .iter()
            .chain(private.iter())
            .map(|x| match x.to_u128() {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err("nonboolean witness"),
            })
            .collect::<Result<crate::core::bits::PackedBits, _>>()?;
        let extra = self.witness_recipe.evaluate(&inputs)?;
        private
            .extend((0..extra.len()).map(|i| {
                crate::runtime::algebra::gf2_128::Gf2_128::from(u128::from(extra.get(i)))
            }));
        Ok(())
    }
    pub fn digest(&self) -> [u8; 32] {
        Sha256::digest(self.to_bytes()).into()
    }
}
