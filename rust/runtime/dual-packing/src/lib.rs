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

//! Standalone flat trace adapter from bit-linear claims to packed GF128 claims.
//!
//! The caller commits polynomial-basis packed words, auxiliaries, 127 independent
//! masks and their checksum before any challenges. It must authenticate the
//! returned equation; this module does not depend on a commitment backend.
pub mod field;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::algebra::RuntimeField;
use crate::runtime::algebra::{
    gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    AlgebraicField,
};
pub use crate::runtime::proto::dual_packing::{
    DualPacking128Proof, DUAL_PACKING_MASK_CELLS, DUAL_PACKING_MESSAGES, PACKING_BASIS_ID,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineClaim {
    pub constant: E,
    pub terms: Vec<(usize, E)>,
}
impl AffineClaim {
    pub fn evaluate(&self, auxiliary: &[E], f: &F) -> Result<E, String> {
        let mut value = self.constant;
        for &(i, k) in &self.terms {
            let x = auxiliary
                .get(i)
                .ok_or("dual packing auxiliary index out of range")?;
            f.add(&mut value, &f.mulf(&k, x));
        }
        Ok(value)
    }
}
/// rhs(auxiliary) = sum_i weights[i]*bit[i].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitLinearClaim {
    pub weights: Vec<E>,
    pub rhs: AffineClaim,
    pub auxiliary_count: usize,
}
impl BitLinearClaim {
    pub fn validate(&self) -> Result<(), String> {
        if self
            .rhs
            .terms
            .iter()
            .any(|&(i, _)| i >= self.auxiliary_count)
        {
            return Err("dual packing auxiliary index out of range".into());
        }
        self.weights
            .len()
            .checked_add(127)
            .ok_or("dual packing bit count overflow")?;
        Ok(())
    }
}
/// rhs(auxiliary)+offset = dot(weights,packed)+dot(mask_weights,R)+checksum_weight*S.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedLinearClaim {
    pub weights: Vec<E>,
    pub rhs: AffineClaim,
    pub offset: E,
    pub mask_weights: [E; DUAL_PACKING_MESSAGES],
    pub checksum_weight: E,
}
impl PackedLinearClaim {
    pub fn residual(
        &self,
        packed: &[E],
        auxiliary: &[E],
        cells: &[E; DUAL_PACKING_MASK_CELLS],
        f: &F,
    ) -> Result<E, String> {
        if packed.len() != self.weights.len() {
            return Err("dual packing packed word count mismatch".into());
        }
        let mut value = self.rhs.evaluate(auxiliary, f)?;
        f.add(&mut value, &self.offset);
        for (a, x) in self.weights.iter().zip(packed) {
            f.add(&mut value, &f.mulf(a, x));
        }
        for (a, x) in self.mask_weights.iter().zip(cells) {
            f.add(&mut value, &f.mulf(a, x));
        }
        f.add(
            &mut value,
            &f.mulf(&self.checksum_weight, &cells[DUAL_PACKING_MESSAGES]),
        );
        Ok(value)
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn inverse_twists(beta: E, f: &F) -> [E; DUAL_PACKING_MESSAGES] {
    let mut powers = [beta; 128];
    for t in 1..128 {
        powers[t] = f.mulf(&powers[t - 1], &powers[t - 1]);
    }
    std::array::from_fn(|index| powers[127 - index])
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn reconstruct(
    basis: &field::PolynomialBasis128,
    claim: &BitLinearClaim,
    proof: &DualPacking128Proof,
    beta: E,
    gamma: &[E; DUAL_PACKING_MESSAGES],
    f: &F,
) -> PackedLinearClaim {
    // Psi(z)=z+sum_{s=1}^{127} gamma_s*z^(2^-s) is binary linear.
    // Write R_ij=sum_h beta_h*r_ijh. Then
    // a_i=sum_h Psi(beta_h)*sum_j dual_j*r_ijh.
    // The transposed dual coordinates share the factor dual_127=1/P'(x).
    let images: [E; 128] = std::array::from_fn(|k| {
        let mut x = E::from(1u128 << k);
        let mut result = x;
        for t in 1..128 {
            x = f.mulf(&x, &x);
            f.add(&mut result, &f.mulf(&gamma[127 - t], &x));
        }
        f.mulf(&basis.dual(127), &result)
    });
    let weights = claim
        .weights
        .chunks(128)
        .map(|row| {
            let numerators = field::dual_coordinate_numerators(row);
            let mut accum = f.zero_accum();
            for (image, coefficient) in images.iter().zip(&numerators) {
                f.mac(&mut accum, image, coefficient);
            }
            f.accum_reduce(&accum)
        })
        .collect();
    let alpha = inverse_twists(beta, f);
    let mut offset = f.zero();
    for (index, &message) in proof.messages.iter().enumerate() {
        f.add(&mut offset, &field::frobenius(message, index + 1, f));
        f.add(&mut offset, &f.mulf(&gamma[index], &message));
    }
    PackedLinearClaim {
        weights,
        rhs: claim.rhs.clone(),
        offset,
        mask_weights: std::array::from_fn(|i| f.mulf(&gamma[i], &alpha[i])),
        checksum_weight: beta,
    }
}
cfg_prover! { pub mod prover; }
cfg_verifier! { pub mod verifier; }
#[cfg(test)]
#[path = "../tests/dual_packing.rs"]
mod tests;
