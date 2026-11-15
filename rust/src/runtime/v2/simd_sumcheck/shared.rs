// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Two fixed frontend claims, one packing reduction and one committed source.
use super::*;
use crate::{core::algebra::AlgebraicField, runtime::algebra::RuntimeField};
pub(crate) struct ScalarClaim {
    pub weights: Vec<E>,
    pub rhs: NativeRow,
}
impl Program {
    pub(super) fn combine(
        &self,
        c: &mut adapter::Claim,
        s: ScalarClaim,
        placements: &[(usize, u8)],
        cells: usize,
        t: &mut TranscriptRef<'_>,
    ) -> Result<(), String> {
        if s.weights.len() != placements.len()
            || cells < self.cell_count()
            || placements.iter().any(|&(w, b)| w >= self.real || b >= 128)
            || s.rhs.terms.iter().any(|&(i, _)| i >= cells)
        {
            return Err("shared SIMD source shape".into());
        }
        let f = F::new();
        let alpha = transcript::scalar_mix(t, &f);
        let count = placements.iter().map(|&(w, _)| w + 1).max().unwrap_or(0);
        let mut indices = [None; 128];
        for (k, &(word, bit)) in s.weights.into_iter().zip(placements) {
            if k == f.zero() {
                continue;
            }
            let index = *indices[bit as usize].get_or_insert_with(|| {
                let i = c.factors.len();
                let mut lanes = [f.zero(); 128];
                lanes[bit as usize] = f.one();
                c.factors.push(adapter::Factor {
                    words: vec![f.zero(); count],
                    lanes,
                });
                i
            });
            f.fma(&mut c.factors[index].words[word], &alpha, &k);
        }
        f.fma(&mut c.rhs.constant, &alpha, &s.rhs.constant);
        c.rhs.terms.extend(
            s.rhs
                .terms
                .into_iter()
                .map(|(i, k)| (i, f.mulf(&alpha, &k))),
        );
        c.auxiliary_count = cells;
        Ok(())
    }
}
