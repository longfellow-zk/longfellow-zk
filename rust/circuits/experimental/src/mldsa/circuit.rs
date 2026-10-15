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

//! Shared field-arithmetic constraints for ML-DSA-44 and ML-DSA-65.

use std::marker::PhantomData;

use circuits_arithmetic::Arithmetic;
use circuits_bitvec::{BitvecLogic, V8};
use circuits_boolean::{Bitw, Boolean};
use compile_logic::{Eltw, Logic, LogicIO};
use core_algebra::SupportsU64Conversions;

use super::{
    algebra::Q,
    params::{MlDsaParams, N},
    reference::ZETAS,
};

pub struct PolynomialW<L: Logic> {
    pub coefficients: [Eltw<L>; N],
}

impl<L: Logic> Clone for PolynomialW<L> {
    fn clone(&self) -> Self {
        Self {
            coefficients: self.coefficients.clone(),
        }
    }
}

impl<L: LogicIO> PolynomialW<L> {
    pub fn input(logic: &L, position: &mut usize) -> Self {
        Self {
            coefficients: std::array::from_fn(|_| logic.next(position)),
        }
    }
}

pub struct MlDsaCircuit<'a, L: Logic, P: MlDsaParams> {
    logic: &'a L,
    _params: PhantomData<P>,
}

impl<'a, L, P> MlDsaCircuit<'a, L, P>
where
    L: Logic,
    L::F: SupportsU64Conversions,
    P: MlDsaParams,
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            _params: PhantomData,
        }
    }

    fn scalar(&self, value: u32) -> <L::F as core_algebra::BareField>::E {
        self.logic.field().u64_to_element(u64::from(value))
    }

    pub fn ntt(&self, polynomial: &PolynomialW<L>) -> PolynomialW<L> {
        let mut result = polynomial.clone();
        let mut k = 1;
        let mut len = N / 2;
        while len >= 1 {
            for start in (0..N).step_by(2 * len) {
                let zeta = self.scalar(ZETAS[k]);
                k += 1;
                for j in start..start + len {
                    let product = self.logic.mulk(&zeta, &result.coefficients[j + len]);
                    let low = self.logic.add(&result.coefficients[j], &product);
                    let high = self.logic.sub(&result.coefficients[j], &product);
                    result.coefficients[j] = low;
                    result.coefficients[j + len] = high;
                }
            }
            len >>= 1;
        }
        debug_assert_eq!(k, N);
        result
    }

    pub fn inverse_ntt(&self, polynomial: &PolynomialW<L>) -> PolynomialW<L> {
        let mut result = polynomial.clone();
        let mut k = N - 1;
        let mut len = 1;
        while len < N {
            for start in (0..N).step_by(2 * len) {
                let neg_zeta = self.scalar(Q - ZETAS[k]);
                k -= 1;
                for j in start..start + len {
                    let low = result.coefficients[j].clone();
                    let sum = self.logic.add(&low, &result.coefficients[j + len]);
                    let difference = self.logic.sub(&low, &result.coefficients[j + len]);
                    result.coefficients[j] = sum;
                    result.coefficients[j + len] = self.logic.mulk(&neg_zeta, &difference);
                }
            }
            len <<= 1;
        }
        debug_assert_eq!(k, 0);
        let inverse_n = self.scalar(8_347_681);
        for coefficient in &mut result.coefficients {
            *coefficient = self.logic.mulk(&inverse_n, coefficient);
        }
        result
    }

    pub fn assert_equal(
        &self,
        name: &str,
        actual: &PolynomialW<L>,
        expected: &PolynomialW<L>,
    ) -> L::Assertions {
        self.logic.assert_mapi(name, 0..N, |i| {
            self.logic.assert_eq(
                "coefficient",
                &actual.coefficients[i],
                &expected.coefficients[i],
            )
        })
    }

    pub fn assert_ntt(
        &self,
        polynomial: &PolynomialW<L>,
        expected: &PolynomialW<L>,
    ) -> L::Assertions {
        self.assert_equal("ntt", &self.ntt(polynomial), expected)
    }

    pub fn assert_inverse_ntt(
        &self,
        polynomial: &PolynomialW<L>,
        expected: &PolynomialW<L>,
    ) -> L::Assertions {
        self.assert_equal("inverse_ntt", &self.inverse_ntt(polynomial), expected)
    }

    pub fn matrix_vector_mul(
        &self,
        matrix: &[Vec<PolynomialW<L>>],
        vector: &[PolynomialW<L>],
    ) -> Vec<PolynomialW<L>> {
        assert_eq!(matrix.len(), P::K);
        assert_eq!(vector.len(), P::L);
        matrix
            .iter()
            .map(|row| {
                assert_eq!(row.len(), P::L);
                PolynomialW {
                    coefficients: std::array::from_fn(|coefficient| {
                        let products: Vec<_> = row
                            .iter()
                            .zip(vector)
                            .map(|(a, x)| {
                                self.logic
                                    .mul(&a.coefficients[coefficient], &x.coefficients[coefficient])
                            })
                            .collect();
                        self.logic.sum(&products)
                    }),
                }
            })
            .collect()
    }

    pub fn pointwise_vector_mul(
        &self,
        scalar: &PolynomialW<L>,
        vector: &[PolynomialW<L>],
    ) -> Vec<PolynomialW<L>> {
        assert_eq!(vector.len(), P::K);
        vector
            .iter()
            .map(|polynomial| PolynomialW {
                coefficients: std::array::from_fn(|i| {
                    self.logic
                        .mul(&scalar.coefficients[i], &polynomial.coefficients[i])
                }),
            })
            .collect()
    }

    fn constant_bits(&self, width: usize, value: u64) -> Vec<Bitw<L>> {
        let boolean = Boolean::new(self.logic);
        (0..width)
            .map(|bit| boolean.konst((value >> bit) & 1 != 0))
            .collect()
    }

    /// Constrains one coefficient of FIPS 204 `UseHint` using the interval-shift
    /// construction from the C++ circuit. `raw_bits` and `hinted_bits` are
    /// little-endian, and `aux_bits` has `P::r0_bits() + 1` bits.
    #[allow(clippy::too_many_arguments)]
    pub fn assert_use_hint_single(
        &self,
        hint: &Eltw<L>,
        value: &Eltw<L>,
        raw_high: &Eltw<L>,
        raw_bits: &[Bitw<L>],
        aux_bits: &[Bitw<L>],
        hinted_high: &Eltw<L>,
        hinted_bits: &[Bitw<L>],
    ) -> L::Assertions {
        assert_eq!(raw_bits.len(), P::R1_BITS);
        assert_eq!(hinted_bits.len(), P::R1_BITS);
        assert_eq!(aux_bits.len(), P::r0_bits() + 1);
        let arithmetic = Arithmetic::new(self.logic);
        let boolean = Boolean::new(self.logic);
        let hint_bit = boolean.of_eltw(hint.clone());
        let raw_reconstructed = arithmetic.as_eltw_field(raw_bits);
        let hinted_reconstructed = arithmetic.as_eltw_field(hinted_bits);
        let raw_in_range = arithmetic.leq(
            raw_bits,
            &self.constant_bits(P::R1_BITS, u64::from(P::use_hint_modulus() - 1)),
        );
        let hinted_in_range = arithmetic.leq(
            hinted_bits,
            &self.constant_bits(P::R1_BITS, u64::from(P::use_hint_modulus() - 1)),
        );
        let r0_width = P::r0_bits();
        let shifted_low = &aux_bits[..r0_width];
        let shifted = arithmetic.as_eltw_field(shifted_low);
        let shifted_in_range = arithmetic.leq(
            shifted_low,
            &self.constant_bits(r0_width, u64::from(2 * P::GAMMA2)),
        );
        let non_positive = &aux_bits[r0_width];
        let sign_expected = arithmetic.leq(
            shifted_low,
            &self.constant_bits(r0_width, u64::from(P::GAMMA2)),
        );
        let hint_element = boolean.as_eltw(&hint_bit);
        let sign_element = boolean.as_eltw(non_positive);
        let twice_hint = self.logic.add(&hint_element, &hint_element);
        let correction = self
            .logic
            .sub(&hint_element, &self.logic.mul(&twice_hint, &sign_element));
        let two_gamma2 = self.scalar(2 * P::GAMMA2);
        let gamma2 = self.scalar(P::GAMMA2);
        let decomposed = self.logic.add(
            &self.logic.mulk(&two_gamma2, raw_high),
            &self.logic.sub(&shifted, &self.logic.konst(&gamma2)),
        );
        let difference = self.logic.sub(raw_high, hinted_high);
        let shifted_difference = self.logic.add(&difference, &correction);
        let modulus = self.logic.konst(&self.scalar(P::use_hint_modulus()));
        let congruence = self.logic.mul(
            &shifted_difference,
            &self.logic.mul(
                &self.logic.sub(&shifted_difference, &modulus),
                &self.logic.add(&shifted_difference, &modulus),
            ),
        );
        self.logic.assert_all(
            "use_hint",
            &[
                self.logic
                    .assert_eq("raw_reconstruction", raw_high, &raw_reconstructed),
                boolean.assert_true("raw_range", &raw_in_range),
                boolean.assert_true("remainder_range", &shifted_in_range),
                boolean.assert_eq("remainder_sign", non_positive, &sign_expected),
                self.logic.assert_eq("decomposition", value, &decomposed),
                self.logic
                    .assert_eq("hinted_reconstruction", hinted_high, &hinted_reconstructed),
                boolean.assert_true("hinted_range", &hinted_in_range),
                self.logic.assert0("hint_congruence", &congruence),
            ],
        )
    }

    pub fn assert_infinity_norm(
        &self,
        name: &str,
        vector: &[PolynomialW<L>],
        shifted_bits: &[Vec<Vec<Bitw<L>>>],
        width: usize,
        bound: u32,
    ) -> L::Assertions {
        assert_eq!(vector.len(), shifted_bits.len());
        let arithmetic = Arithmetic::new(self.logic);
        let boolean = Boolean::new(self.logic);
        self.logic.assert_mapi(name, 0..vector.len() * N, |index| {
            let polynomial = index / N;
            let coefficient = index % N;
            let bits = &shifted_bits[polynomial][coefficient];
            assert_eq!(bits.len(), width);
            let reconstructed = arithmetic.as_eltw_field(bits);
            let shifted = self.logic.add(
                &vector[polynomial].coefficients[coefficient],
                &self.logic.konst(&self.scalar(bound - 1)),
            );
            let in_range =
                arithmetic.leq(bits, &self.constant_bits(width, u64::from(2 * bound - 2)));
            self.logic.assert_all(
                "coefficient",
                &[
                    self.logic
                        .assert_eq("reconstruction", &shifted, &reconstructed),
                    boolean.assert_true("range", &in_range),
                ],
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub fn assert_use_hint(
        &self,
        hints: &[PolynomialW<L>],
        approximations: &[PolynomialW<L>],
        raw_high: &[PolynomialW<L>],
        raw_bits: &[Vec<Vec<Bitw<L>>>],
        auxiliary_bits: &[Vec<Vec<Bitw<L>>>],
        hinted_high: &[PolynomialW<L>],
        hinted_bits: &[Vec<Vec<Bitw<L>>>],
        hint_sum_bits: &[Bitw<L>],
    ) -> L::Assertions {
        for collection_len in [
            hints.len(),
            approximations.len(),
            raw_high.len(),
            raw_bits.len(),
            auxiliary_bits.len(),
            hinted_high.len(),
            hinted_bits.len(),
        ] {
            assert_eq!(collection_len, P::K);
        }
        let mut assertions = Vec::with_capacity(P::K * N + 2);
        let mut hint_terms = Vec::with_capacity(P::K * N);
        for polynomial in 0..P::K {
            for coefficient in 0..N {
                assertions.push(self.assert_use_hint_single(
                    &hints[polynomial].coefficients[coefficient],
                    &approximations[polynomial].coefficients[coefficient],
                    &raw_high[polynomial].coefficients[coefficient],
                    &raw_bits[polynomial][coefficient],
                    &auxiliary_bits[polynomial][coefficient],
                    &hinted_high[polynomial].coefficients[coefficient],
                    &hinted_bits[polynomial][coefficient],
                ));
                hint_terms.push(hints[polynomial].coefficients[coefficient].clone());
            }
        }
        let arithmetic = Arithmetic::new(self.logic);
        let boolean = Boolean::new(self.logic);
        let sum_width = (usize::BITS - P::OMEGA.leading_zeros()) as usize;
        assert_eq!(hint_sum_bits.len(), sum_width);
        let reconstructed_sum = arithmetic.as_eltw_field(hint_sum_bits);
        assertions.push(self.logic.assert_eq(
            "hint_sum",
            &self.logic.sum(&hint_terms),
            &reconstructed_sum,
        ));
        assertions.push(boolean.assert_true(
            "hint_weight",
            &arithmetic.leq(
                hint_sum_bits,
                &self.constant_bits(sum_width, P::OMEGA as u64),
            ),
        ));
        self.logic.assert_all("all_hints", &assertions)
    }

    pub fn assert_w1_encode(
        &self,
        coefficients: &[Vec<Vec<Bitw<L>>>],
        encoded: &[V8<L>],
    ) -> L::Assertions {
        assert_eq!(coefficients.len(), P::K);
        assert_eq!(encoded.len(), P::K * P::W1_BYTES);
        let bitvec = BitvecLogic::new(self.logic);
        let all_bits: Vec<_> = coefficients
            .iter()
            .flat_map(|polynomial| {
                assert_eq!(polynomial.len(), N);
                polynomial.iter().flat_map(|bits| {
                    assert_eq!(bits.len(), P::R1_BITS);
                    bits.iter().cloned()
                })
            })
            .collect();
        self.logic.assert_mapi("w1_encode", 0..encoded.len(), |i| {
            let byte = V8::new(
                (0..8)
                    .map(|bit| {
                        all_bits
                            .get(i * 8 + bit)
                            .cloned()
                            .unwrap_or_else(|| Boolean::new(self.logic).falseb())
                    })
                    .collect(),
            );
            bitvec.assert_eq("byte", &encoded[i], &byte)
        })
    }

    /// Constrains `w = InvNTT(A .* NTT(z) - NTT(c) .* ntt_t1)`.
    #[allow(clippy::too_many_arguments)]
    pub fn assert_w_approximation(
        &self,
        matrix: &[Vec<PolynomialW<L>>],
        ntt_t1: &[PolynomialW<L>],
        z: &[PolynomialW<L>],
        c: &PolynomialW<L>,
        ntt_z: &[PolynomialW<L>],
        ntt_c: &PolynomialW<L>,
        w: &[PolynomialW<L>],
    ) -> L::Assertions {
        assert_eq!(ntt_t1.len(), P::K);
        assert_eq!(z.len(), P::L);
        assert_eq!(ntt_z.len(), P::L);
        assert_eq!(w.len(), P::K);
        let mut assertions = Vec::with_capacity(P::L + P::K + 1);
        for i in 0..P::L {
            assertions.push(self.assert_ntt(&z[i], &ntt_z[i]));
        }
        assertions.push(self.assert_ntt(c, ntt_c));
        let az = self.matrix_vector_mul(matrix, ntt_z);
        let ct1 = self.pointwise_vector_mul(ntt_c, ntt_t1);
        for i in 0..P::K {
            let difference = PolynomialW {
                coefficients: std::array::from_fn(|j| {
                    self.logic
                        .sub(&az[i].coefficients[j], &ct1[i].coefficients[j])
                }),
            };
            assertions.push(self.assert_inverse_ntt(&difference, &w[i]));
        }
        self.logic.assert_all("w_approximation", &assertions)
    }
}
