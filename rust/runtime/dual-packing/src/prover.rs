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

//! One masked response; no inner sumcheck and no tower-field operations.
use super::{
    field::{self, PolynomialBasis128},
    BitLinearClaim, DualPacking128Proof, PackedLinearClaim, DUAL_PACKING_MASK_CELLS,
    DUAL_PACKING_MESSAGES,
};
use crate::{
    core::bits::PackedBits,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            AlgebraicField, RuntimeField,
        },
        random::{RandomEngine, Transcript},
    },
};

pub struct DualPackingMaskValues {
    random: [E; DUAL_PACKING_MESSAGES],
    checksum: E,
}
impl DualPackingMaskValues {
    pub fn sample(rng: &mut impl RandomEngine, f: &F) -> Self {
        let random = std::array::from_fn(|_| E::from(rng.u128()));
        let mut checksum = f.zero();
        for (index, &r) in random.iter().enumerate() {
            f.add(&mut checksum, &field::frobenius(r, index + 1, f));
        }
        Self { random, checksum }
    }
    pub fn cells(&self) -> [E; DUAL_PACKING_MASK_CELLS] {
        std::array::from_fn(|i| {
            if i < DUAL_PACKING_MESSAGES {
                self.random[i]
            } else {
                self.checksum
            }
        })
    }
}
/// Write R[i,j]=sum_h beta_h*r[i,j,h], with binary r. Transpose each public
/// coefficient row, then compute Z[h]=sum_(i,j) X[i]*dual_j*r[i,j,h].
/// The original components are V_s=sum_h beta_h^(2^-s)*Z[h]. This moves all
/// Frobenius operations past the large witness sum and keeps only 128 fields.
pub(super) fn components(
    basis: &PolynomialBasis128,
    weights: &[E],
    bits: &PackedBits,
    f: &F,
) -> [E; DUAL_PACKING_MESSAGES] {
    if weights.is_empty() {
        return [f.zero(); DUAL_PACKING_MESSAGES];
    }
    let mut accum = std::array::from_fn::<_, 128, _>(|_| f.zero_accum());
    for (i, row) in weights.chunks(128).enumerate() {
        let numerators = field::dual_coordinate_numerators(row);
        let word = E::from(bits.word128(i));
        for (a, coefficient) in accum.iter_mut().zip(&numerators) {
            f.mac(a, &word, coefficient);
        }
    }
    // All dual basis elements share the denominator P'(x)=x^6+1.
    let z = accum.map(|a| f.mulf(&basis.dual(127), &f.accum_reduce(&a)));
    let mut values = [f.zero(); DUAL_PACKING_MESSAGES];
    let mut point = E::from(2); // beta_h=x^h, so evaluate Z(T) at x^(2^-s).
    for t in 1..128 {
        point = f.mulf(&point, &point);
        let mut value = z[127];
        for coefficient in z[..127].iter().rev() {
            value = f.addf(&f.mulf(&value, &point), coefficient);
        }
        values[127 - t] = value;
    }
    values
}
pub fn reduce(
    basis: &PolynomialBasis128,
    claim: &BitLinearClaim,
    bits: &PackedBits,
    masks: DualPackingMaskValues,
    context: &[u8],
    ts: &mut Transcript,
    f: &F,
) -> Result<(DualPacking128Proof, PackedLinearClaim), String> {
    claim.validate()?;
    if bits.len() != claim.weights.len() {
        return Err("dual packing logical bit count mismatch".into());
    }
    let beta = super::transcript::begin(claim, context, ts, f);
    let values = components(basis, &claim.weights, bits, f);
    let alpha = super::inverse_twists(beta, f);
    let proof = DualPacking128Proof {
        messages: std::array::from_fn(|i| f.addf(&values[i], &f.mulf(&alpha[i], &masks.random[i]))),
    };
    let gamma = super::transcript::batch(&proof, ts, f);
    let result = super::reconstruct(basis, claim, &proof, beta, &gamma, f);
    Ok((proof, result))
}
