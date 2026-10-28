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

//! Trace-pairing adapter from bit-linear claims to two packed GF128 equations.
//!
//! The caller commits packed words, auxiliaries, 127 free masks and scalar cells
//! r,b before challenges. Honest setup sets b=r^2; the verifier does not enforce
//! that relation. Both returned linear equations must be authenticated.
pub mod field;
pub mod generic;
mod generic_codec;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::algebra::RuntimeField;
use crate::runtime::algebra::{
    gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    AlgebraicField,
};
pub use crate::runtime::proto::dual_packing::{
    DualPacking128Proof, DUAL_PACKING_COORDINATES, DUAL_PACKING_FREE_MASKS,
    DUAL_PACKING_MASK_CELLS, PACKING_BASIS_ID,
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
/// rhs(auxiliary)+offset = dot(weights,packed)+dot(mask_weights,cells).
/// Empty weights mean the equation does not use the packed words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedLinearClaim {
    pub weights: Vec<E>,
    pub rhs: AffineClaim,
    pub offset: E,
    pub mask_weights: [E; DUAL_PACKING_MASK_CELLS],
}
impl PackedLinearClaim {
    pub fn residual(
        &self,
        packed: &[E],
        auxiliary: &[E],
        cells: &[E; DUAL_PACKING_MASK_CELLS],
        f: &F,
    ) -> Result<E, String> {
        if !self.weights.is_empty() && packed.len() != self.weights.len() {
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
        Ok(value)
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn validate_traces(
    basis: &field::PolynomialBasis128,
    u: &[E; DUAL_PACKING_COORDINATES],
) -> Result<(), String> {
    if u.iter().any(|&value| basis.trace_bit(value)) {
        return Err("dual packing response has nonzero trace".into());
    }
    Ok(())
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn reconstruct(
    basis: &field::PolynomialBasis128,
    claim: &BitLinearClaim,
    proof: &DualPacking128Proof,
    delta: &[E; DUAL_PACKING_COORDINATES],
    f: &F,
) -> [PackedLinearClaim; 2] {
    let gamma = delta.map(|x| f.mulf(&x, &x));
    // D_ik = sum_j alpha_j * digit_k(R_ij). The existing transpose returns
    // D_ik/alpha_127, so move that common factor into the public weights.
    let images = gamma.map(|x| f.mulf(&x, &basis.dual(127)));
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
    let beta: [E; 128] = std::array::from_fn(|j| E::from(1u128 << j));
    let dual: [E; 128] = std::array::from_fn(|j| basis.dual(j));
    let rhs = generic::Affine {
        constant: claim.rhs.constant,
        terms: claim.rhs.terms.clone(),
    };
    let equations = generic::native_equations(
        f,
        &beta,
        &dual,
        &rhs,
        &proof.u,
        &proof.a,
        delta,
        &gamma,
        &f.mulf(&proof.a, &proof.a),
        weights,
    );
    equations.map(|eq| PackedLinearClaim {
        weights: eq.words,
        rhs: AffineClaim {
            constant: f.zero(),
            terms: eq.auxiliary,
        },
        offset: eq.constant,
        mask_weights: eq.masks.try_into().expect("fixed GF128 mask count"),
    })
}
cfg_prover! { pub mod prover; }
cfg_verifier! { pub mod verifier; }
#[cfg(test)]
#[path = "../tests/generic.rs"]
mod generic_tests;
#[cfg(test)]
#[path = "../tests/dual_packing.rs"]
mod tests;
