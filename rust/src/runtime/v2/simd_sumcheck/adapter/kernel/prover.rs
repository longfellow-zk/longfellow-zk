// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::algebra::RuntimeField;
enum Matrix {
    Coordinate,
    General(Vec<[E; 128]>),
}
pub(in crate::runtime::v2::simd_sumcheck::adapter) struct Kernel {
    matrices: Vec<Matrix>,
    coordinates: Vec<(usize, [E; 128])>,
}
impl Kernel {
    pub(in crate::runtime::v2::simd_sumcheck::adapter) fn new(claim: &Claim, f: &F) -> Self {
        let matrices: Vec<_> = claim
            .factors
            .iter()
            .map(|factor| {
                if coordinate(&factor.lanes).is_some() {
                    return Matrix::Coordinate;
                }
                let rows = (0..128)
                    .map(|h| {
                        let row = factor.lanes.map(|v| f.mulf(&E::from(1u128 << h), &v));
                        dual_coordinate_numerators(&row)
                    })
                    .collect();
                Matrix::General(rows)
            })
            .collect();
        let coordinates = coordinate_rows(claim).collect();
        Self {
            matrices,
            coordinates,
        }
    }
    pub(in crate::runtime::v2::simd_sumcheck::adapter) fn components(
        &self,
        claim: &Claim,
        packed: &[E],
        parameters: &Parameters,
        f: &F,
    ) -> [E; 128] {
        let mut b = std::array::from_fn::<_, 128, _>(|_| f.zero_accum());
        for (word, coefficients) in &self.coordinates {
            for (a, k) in b.iter_mut().zip(coefficients) {
                f.mac(a, k, &packed[*word]);
            }
        }
        for (p, m) in claim.factors.iter().zip(&self.matrices) {
            let Matrix::General(rows) = m else { continue };
            let mut sums = [f.zero(); 128];
            for (k, word) in p.words.iter().zip(packed) {
                let mut mask = k.to_u128();
                while mask != 0 {
                    sums[mask.trailing_zeros() as usize].xor_in_place(word);
                    mask &= mask - 1;
                }
            }
            for (row, s) in rows.iter().zip(sums) {
                for (a, coefficient) in b.iter_mut().zip(row) {
                    f.mac(a, coefficient, &s);
                }
            }
        }
        b.map(|a| f.mulf(&parameters.dual()[127], &f.accum_reduce(&a)))
    }
    pub(in crate::runtime::v2::simd_sumcheck::adapter) fn weights(
        &self,
        claim: &Claim,
        delta: &[E; 128],
        parameters: &Parameters,
        f: &F,
    ) -> Vec<E> {
        let gamma = delta.map(|d| f.mulf(&d, &d));
        let mut weights = vec![
            f.zero();
            claim
                .factors
                .iter()
                .map(|factor| factor.words.len())
                .max()
                .unwrap_or(0)
        ];
        for (word, row) in &self.coordinates {
            weights[*word] = f.mulf(&parameters.dual()[127], &dot(row, &gamma, f));
        }
        for (p, m) in claim.factors.iter().zip(&self.matrices) {
            let Matrix::General(rows) = m else {
                continue;
            };
            let images = std::array::from_fn(|h| {
                let mut a = f.zero_accum();
                for (coefficient, g) in rows[h].iter().zip(&gamma) {
                    f.mac(&mut a, coefficient, g);
                }
                f.mulf(&parameters.dual()[127], &f.accum_reduce(&a))
            });
            accumulate_map(&mut weights, &p.words, &images, f);
        }
        weights
    }
}
