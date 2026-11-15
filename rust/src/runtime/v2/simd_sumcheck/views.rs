// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public GF(2)-linear views of packed words. A view permutes or projects bits;
//! its transpose pulls bit-functionals back to the original committed words.
use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use super::{adapter::Factor, E, F};
use crate::{core::algebra::AlgebraicField, runtime::algebra::RuntimeField};

/// A partial permutation: destination bit j reads at most one source bit.
/// No source bit may be duplicated. Missing destination bits are zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitPermutation {
    sources: [Option<u8>; 128],
    runs: Vec<(u128, i16)>,
}
impl BitPermutation {
    pub fn new(sources: [Option<u8>; 128]) -> Result<Self, String> {
        let mut used = 0u128;
        let mut runs = BTreeMap::<i16, u128>::new();
        for (destination, entry) in sources.iter().enumerate() {
            if let Some(source) = entry {
                if *source >= 128 || used & (1u128 << source) != 0 {
                    return Err("partial bit permutation duplicates or exceeds a source".into());
                }
                used |= 1u128 << source;
                *runs
                    .entry(destination as i16 - i16::from(*source))
                    .or_default() |= 1u128 << source;
            }
        }
        Ok(Self {
            sources,
            runs: runs
                .into_iter()
                .map(|(shift, mask)| (mask, shift))
                .collect(),
        })
    }
    pub fn identity() -> Self {
        Self::new(std::array::from_fn(|j| Some(j as u8))).expect("identity permutation")
    }
    pub fn sources(&self) -> &[Option<u8>; 128] {
        &self.sources
    }
    pub fn apply(&self, word: u128) -> u128 {
        self.runs.iter().fold(0, |out, (mask, shift)| {
            out ^ if *shift >= 0 {
                (word & mask) << (*shift as u32)
            } else {
                (word & mask) >> ((-*shift) as u32)
            }
        })
    }
    fn transpose(&self, lanes: &[E; 128]) -> [E; 128] {
        let mut out = [E::from(0); 128];
        for (j, entry) in self.sources.iter().enumerate() {
            if let Some(source) = entry {
                out[usize::from(*source)].xor_in_place(&lanes[j]);
            }
        }
        out
    }
}
/// One committed source word viewed through a public partial permutation.
/// The mapped program constructor validates both indices against its tables.
#[derive(Clone, Debug)]
pub struct MappedTerm {
    pub word: usize,
    pub map: usize,
}
/// XOR of mapped committed words and one arbitrary public constant word.
#[derive(Clone, Debug)]
pub struct BitAffineInput {
    pub terms: Vec<MappedTerm>,
    pub constant: u128,
}

pub(super) struct BitViews {
    pub maps: Vec<BitPermutation>,
    pub forms: Vec<BitAffineInput>,
}
impl BitViews {
    pub(super) fn new(
        real: usize,
        maps: Vec<BitPermutation>,
        forms: Vec<BitAffineInput>,
    ) -> Result<Self, String> {
        if maps.first() != Some(&BitPermutation::identity())
            || forms
                .iter()
                .flat_map(|a| &a.terms)
                .any(|t| t.word >= real || t.map >= maps.len())
        {
            return Err("mapped affine source shape or identity map".into());
        }
        Ok(Self { maps, forms })
    }
    pub(super) fn hash_into(&self, h: &mut Sha256) {
        h.update(self.metadata_bytes());
    }
    pub(super) fn metadata_bytes(&self) -> Vec<u8> {
        let mut out = b"BITVIEWS1".to_vec();
        out.extend((self.maps.len() as u64).to_le_bytes());
        for map in &self.maps {
            out.extend(map.sources.map(|x| x.unwrap_or(128)));
        }
        out.extend((self.forms.len() as u64).to_le_bytes());
        for form in &self.forms {
            out.extend(form.constant.to_le_bytes());
            out.extend((form.terms.len() as u64).to_le_bytes());
            for term in &form.terms {
                out.extend((term.word as u64).to_le_bytes());
                out.extend((term.map as u64).to_le_bytes());
            }
        }
        out
    }

    /// Pull a separable functional back through each public map. Terms with
    /// the same map retain separability; constants move to the affine RHS.
    pub(super) fn pullback(
        &self,
        real: usize,
        wires: &[usize],
        weights: &[E],
        lanes: &[E; 128],
    ) -> (Vec<Factor>, E) {
        let f = F::new();
        let mut grouped = vec![vec![f.zero(); real]; self.maps.len()];
        let mut offset = f.zero();
        for (&wire, k) in wires.iter().zip(weights) {
            if *k == f.zero() {
                continue;
            }
            if wire < real {
                f.add(&mut grouped[0][wire], k);
            } else {
                let form = &self.forms[wire - real];
                let mut bits = form.constant;
                let mut value = f.zero();
                while bits != 0 {
                    value.xor_in_place(&lanes[bits.trailing_zeros() as usize]);
                    bits &= bits - 1;
                }
                f.fma(&mut offset, k, &value);
                for term in &form.terms {
                    f.add(&mut grouped[term.map][term.word], k);
                }
            }
        }
        let factors = grouped
            .into_iter()
            .zip(&self.maps)
            .filter(|(words, _)| words.iter().any(|x| *x != f.zero()))
            .map(|(words, map)| Factor {
                words,
                lanes: map.transpose(lanes),
            })
            .collect();
        (factors, offset)
    }
}

#[cfg(test)]
mod tests;

cfg_prover! {mod prover;}
