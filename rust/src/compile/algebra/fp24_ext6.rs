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

use crate::core::algebra::fp24_ext6::{
    add_extension, deserialize, invert_extension, mul_extension, serialize, sub_extension,
};
pub use crate::core::algebra::fp24_ext6::{
    BASE_SERIALIZED_SIZE, BETA, EXTENSION_DEGREE, Q, SERIALIZED_SIZE,
};
use crate::core::algebra::{AlgebraicField, BareField, SerializableField, SupportsU64Conversions};

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
        add_extension(&mut a.coefficients, &b.coefficients);
    }

    fn sub(&self, a: &mut Self::E, b: &Self::E) {
        sub_extension(&mut a.coefficients, &b.coefficients);
    }

    fn mul(&self, a: &mut Self::E, b: &Self::E) {
        mul_extension(&mut a.coefficients, &b.coefficients);
    }

    fn invert(&self, a: &Self::E) -> Self::E {
        CompileElement::new(invert_extension(&a.coefficients))
    }
}

impl crate::core::algebra::Comparable for CompileFp24Ext6 {
    fn compare(&self, a: &Self::E, b: &Self::E) -> std::cmp::Ordering {
        a.coefficients.cmp(&b.coefficients)
    }
}

impl SerializableField for CompileFp24Ext6 {
    fn field_id(&self) -> crate::core::algebra::FieldID {
        crate::core::algebra::FieldID::None
    }
    fn is_binary(&self) -> bool {
        false
    }

    fn serialized_size_bytes(&self) -> usize {
        SERIALIZED_SIZE
    }

    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        serialize(&e.coefficients, dst);
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        deserialize(bytes).map(CompileElement::new)
    }

    fn serialized_mone(&self) -> Vec<u8> {
        self.to_bytes(&self.mone())
    }
}

impl crate::core::algebra::HasLookupPoints for CompileFp24Ext6 {
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

impl crate::core::algebra::SupportsU128Conversions for CompileFp24Ext6 {
    fn u128_to_element(&self, n: u128) -> Self::E {
        assert!(n < u128::from(Q), "integer is not a canonical F_q element");
        self.u64_to_element(n as u64)
    }
}

impl crate::compile::algebra::CompileField for CompileFp24Ext6 {
    fn characteristic(&self) -> num_bigint::BigUint {
        Q.into()
    }

    fn pseudo_basis(&self, i: usize) -> Self::E {
        assert!(i < self.pseudo_dimension());
        self.u64_to_element(1u64 << i)
    }

    fn pseudo_dimension(&self) -> usize {
        22
    }

    fn pseudo_basis_unsafe(&self, i: usize) -> Self::E {
        let value = num_bigint::BigUint::from(2u32).modpow(&i.into(), &Q.into());
        let digits = value.to_u32_digits();
        self.u64_to_element(u64::from(digits.first().copied().unwrap_or(0)))
    }

    fn pseudo_dimension_of_multiplicative_group(&self) -> usize {
        let order = num_bigint::BigUint::from(Q).pow(EXTENSION_DEGREE as u32) - 1u32;
        (order.bits() - 1) as usize
    }
}
