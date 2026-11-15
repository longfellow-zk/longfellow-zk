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

//! Compiler field for the sextic extension `F_q[x] / (x^6 - 7)`.
//! Its elements remain distinct from runtime elements.

use num_bigint::BigUint;

use crate::{
    compile::algebra::CompileField,
    core::algebra::{
        fp24::{BASE_SERIALIZED_SIZE, BETA, EXTENSION_DEGREE, Q, SERIALIZED_SIZE},
        AlgebraicField, BareField, Comparable, FieldID, HasLookupPoints, SerializableField,
        SupportsU128Conversions, SupportsU64Conversions,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompileElement {
    coefficients: [u32; EXTENSION_DEGREE],
}

impl CompileElement {
    fn new(coefficients: [u32; EXTENSION_DEGREE]) -> Self {
        Self { coefficients }
    }

    #[must_use]
    pub fn coefficients(&self) -> &[u32; EXTENSION_DEGREE] {
        &self.coefficients
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompileFp24Ext6;

impl CompileFp24Ext6 {
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    #[must_use]
    pub fn from_coefficients(&self, coefficients: [u32; EXTENSION_DEGREE]) -> CompileElement {
        assert!(coefficients.iter().all(|&coefficient| coefficient < Q));
        CompileElement::new(coefficients)
    }
}

impl BareField for CompileFp24Ext6 {
    type E = CompileElement;
}

impl AlgebraicField for CompileFp24Ext6 {
    fn zero(&self) -> Self::E {
        CompileElement::new([0; EXTENSION_DEGREE])
    }

    fn one(&self) -> Self::E {
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = 1;
        CompileElement::new(coefficients)
    }

    fn add(&self, a: &mut Self::E, b: &Self::E) {
        for (left, right) in a.coefficients.iter_mut().zip(b.coefficients) {
            *left = (*left + right) % Q;
        }
    }

    fn sub(&self, a: &mut Self::E, b: &Self::E) {
        for (left, right) in a.coefficients.iter_mut().zip(b.coefficients) {
            *left = (*left + Q - right) % Q;
        }
    }

    fn mul(&self, a: &mut Self::E, b: &Self::E) {
        // A direct polynomial product is intentionally independent of runtime's
        // delayed accumulator and folded multiplication implementation.
        let mut result = [0u64; EXTENSION_DEGREE];
        for (i, &x) in a.coefficients.iter().enumerate() {
            for (j, &y) in b.coefficients.iter().enumerate() {
                let coefficient = u64::from(x) * u64::from(y);
                result[(i + j) % EXTENSION_DEGREE] += if i + j >= EXTENSION_DEGREE {
                    coefficient * u64::from(BETA)
                } else {
                    coefficient
                };
            }
        }
        a.coefficients = result.map(|value| (value % u64::from(Q)) as u32);
    }

    fn invert(&self, a: &Self::E) -> Self::E {
        assert!(a.coefficients.iter().any(|&x| x != 0), "cannot invert zero");
        if a.coefficients[1..].iter().all(|&x| x == 0) {
            let mut result = 1u64;
            let mut base = u64::from(a.coefficients[0]);
            let mut exponent = Q - 2;
            while exponent != 0 {
                if exponent & 1 != 0 {
                    result = result * base % u64::from(Q);
                }
                base = base * base % u64::from(Q);
                exponent >>= 1;
            }
            return self.u64_to_element(result);
        }
        // Fermat inversion provides an independent check of runtime's
        // Gaussian solve of the multiplication matrix.
        let exponent = BigUint::from(Q).pow(EXTENSION_DEGREE as u32) - 2u32;
        let mut result = self.one();
        let mut base = *a;
        for bit in 0..exponent.bits() {
            if exponent.bit(bit) {
                self.mul(&mut result, &base);
            }
            base = self.mulf(&base, &base);
        }
        result
    }
}

impl Comparable for CompileFp24Ext6 {
    fn compare(&self, a: &Self::E, b: &Self::E) -> std::cmp::Ordering {
        a.coefficients.cmp(&b.coefficients)
    }
}

impl SerializableField for CompileFp24Ext6 {
    fn field_id(&self) -> FieldID {
        FieldID::Fp24Ext6
    }
    fn is_binary(&self) -> bool {
        false
    }

    fn serialized_size_bytes(&self) -> usize {
        SERIALIZED_SIZE
    }

    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(dst.len(), SERIALIZED_SIZE);
        for (coefficient, bytes) in e
            .coefficients
            .iter()
            .zip(dst.as_chunks_mut::<BASE_SERIALIZED_SIZE>().0)
        {
            bytes.copy_from_slice(&coefficient.to_le_bytes()[..BASE_SERIALIZED_SIZE]);
        }
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        if bytes.len() != SERIALIZED_SIZE {
            return Err("invalid Fp24 sextic extension element size".into());
        }
        let mut coefficients = [0; EXTENSION_DEGREE];
        for (coefficient, chunk) in coefficients
            .iter_mut()
            .zip(bytes.as_chunks::<BASE_SERIALIZED_SIZE>().0)
        {
            *coefficient = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], 0]);
            if *coefficient >= Q {
                return Err("non-canonical Fp24 sextic extension coefficient".into());
            }
        }
        Ok(CompileElement::new(coefficients))
    }

    fn serialized_mone(&self) -> Vec<u8> {
        self.to_bytes(&self.mone())
    }
}

impl HasLookupPoints for CompileFp24Ext6 {
    fn lookup_point(&self, n: usize, i: usize) -> Self::E {
        let value =
            ((2 * i) as u64 + u64::from(Q) - ((n - 1) as u64 % u64::from(Q))) % u64::from(Q);
        self.u64_to_element(value)
    }
}

impl SupportsU64Conversions for CompileFp24Ext6 {
    fn u64_to_element(&self, n: u64) -> Self::E {
        assert!(n < u64::from(Q), "integer is not a canonical F_q element");
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = n as u32;
        CompileElement::new(coefficients)
    }
}

impl SupportsU128Conversions for CompileFp24Ext6 {
    fn u128_to_element(&self, n: u128) -> Self::E {
        assert!(n < u128::from(Q), "integer is not a canonical F_q element");
        self.u64_to_element(n as u64)
    }
}

impl CompileField for CompileFp24Ext6 {
    fn pseudo_basis(&self, i: usize) -> Self::E {
        assert!(i < self.pseudo_dimension());
        self.u64_to_element(1u64 << i)
    }

    fn pseudo_dimension(&self) -> usize {
        22
    }

    fn pseudo_basis_unsafe(&self, i: usize) -> Self::E {
        let value = BigUint::from(2u32).modpow(&i.into(), &Q.into());
        let digits = value.to_u32_digits();
        self.u64_to_element(u64::from(digits.first().copied().unwrap_or(0)))
    }

    fn pseudo_dimension_of_multiplicative_group(&self) -> usize {
        let order = BigUint::from(Q).pow(EXTENSION_DEGREE as u32) - 1u32;
        (order.bits() - 1) as usize
    }
}

#[cfg(test)]
mod tests;
