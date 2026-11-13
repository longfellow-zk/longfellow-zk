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

//! Runtime arithmetic, compact serialization and sampling in the sextic field.
//! This module has no compiler or circuit dependencies.

pub use crate::core::algebra::fp24_ext6::{
    BASE_SERIALIZED_SIZE, BETA, EXTENSION_DEGREE, Q, SERIALIZED_SIZE,
};
use crate::{
    core::algebra::{
        fp24::invert_base,
        fp24_ext6::{
            add_extension, deserialize, invert_extension, mul_extension, serialize, sub_extension,
        },
        AlgebraicField, BareField, Nat, SerializableField, SupportsU64Conversions,
    },
    runtime::algebra::{
        field::{RuntimeSerializableField, SupportsSampling},
        poly::InterpolationField,
        RuntimeField, RuntimeNat,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RuntimeElement {
    coefficients: [u32; EXTENSION_DEGREE],
}

impl RuntimeElement {
    pub(in crate::runtime) fn new(coefficients: [u32; EXTENSION_DEGREE]) -> Self {
        Self { coefficients }
    }

    #[must_use]
    pub fn coefficients(&self) -> &[u32; EXTENSION_DEGREE] {
        &self.coefficients
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RuntimeFp24Ext6;

impl RuntimeFp24Ext6 {
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    #[must_use]
    pub fn from_coefficients(&self, coefficients: [u32; EXTENSION_DEGREE]) -> RuntimeElement {
        assert!(coefficients.iter().all(|&coefficient| coefficient < Q));
        RuntimeElement::new(coefficients)
    }
}

impl BareField for RuntimeFp24Ext6 {
    type E = RuntimeElement;
}

impl AlgebraicField for RuntimeFp24Ext6 {
    fn zero(&self) -> Self::E {
        RuntimeElement::new([0; EXTENSION_DEGREE])
    }

    fn one(&self) -> Self::E {
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = 1;
        RuntimeElement::new(coefficients)
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
        RuntimeElement::new(invert_extension(&a.coefficients))
    }
}

impl SerializableField for RuntimeFp24Ext6 {
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
        deserialize(bytes).map(RuntimeElement::new)
    }

    fn serialized_mone(&self) -> Vec<u8> {
        self.to_bytes(&self.mone())
    }
}

impl SupportsU64Conversions for RuntimeFp24Ext6 {
    fn u64_to_element(&self, n: u64) -> Self::E {
        assert!(n < u64::from(Q), "integer is not a canonical F_q element");
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = n as u32;
        RuntimeElement::new(coefficients)
    }
}

impl crate::core::algebra::HasLookupPoints for RuntimeFp24Ext6 {
    fn lookup_point(&self, n: usize, i: usize) -> Self::E {
        let value =
            ((2 * i) as u64 + u64::from(Q) - ((n - 1) as u64 % u64::from(Q))) % u64::from(Q);
        self.u64_to_element(value)
    }
}

impl RuntimeField<3> for RuntimeFp24Ext6 {
    // Keep the degree-ten polynomial unreduced. Each product contributes at
    // most 6*(q-1)^2 to a coefficient. Even a batch of u64::MAX products and
    // the final x^6=7 fold fit below 2^116, well within u128.
    type Accum = [u128; 2 * EXTENSION_DEGREE - 1];

    fn zero_accum(&self) -> Self::Accum {
        [0; 2 * EXTENSION_DEGREE - 1]
    }

    fn mac(&self, acc: &mut Self::Accum, x: &Self::E, y: &Self::E) {
        // One unreduced product fits in u64: at most six 23-bit products
        // contribute to a coefficient. No field or polynomial reduction occurs.
        let product =
            crate::core::algebra::fp24_ext6::product_unreduced(&x.coefficients, &y.coefficients);
        for (coefficient, product) in acc.iter_mut().zip(product) {
            *coefficient += u128::from(product);
        }
    }

    fn accum_reduce(&self, acc: &Self::Accum) -> Self::E {
        RuntimeElement::new(std::array::from_fn(|i| {
            let mut coefficient = acc[i];
            if i + EXTENSION_DEGREE < acc.len() {
                coefficient += u128::from(BETA) * acc[i + EXTENSION_DEGREE];
            }
            (coefficient % u128::from(Q)) as u32
        }))
    }
}

impl RuntimeSerializableField<3> for RuntimeFp24Ext6 {
    fn to_words64(&self, e: &Self::E) -> [u64; 3] {
        let mut bytes = [0u8; 24];
        serialize(&e.coefficients, &mut bytes[..SERIALIZED_SIZE]);
        std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * (i + 1)].try_into().unwrap()))
    }

    fn words64_to_element(&self, words: &[u64; 3]) -> Result<Self::E, String> {
        let mut bytes = [0u8; 24];
        for (word, chunk) in words.iter().zip(bytes.as_chunks_mut::<8>().0.iter_mut()) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        if bytes[SERIALIZED_SIZE..].iter().any(|&byte| byte != 0) {
            return Err("non-canonical Fp24 sextic extension word padding".to_owned());
        }
        deserialize(&bytes[..SERIALIZED_SIZE]).map(RuntimeElement::new)
    }
}

impl crate::core::algebra::SupportsNatConversions<3> for RuntimeFp24Ext6 {
    type N = RuntimeNat<3>;

    fn reduce_nat(&self, n: &Self::N) -> Self::E {
        let value = n
            .to_limbs()
            .iter()
            .rev()
            .flat_map(|word| word.to_be_bytes())
            .fold(0u64, |acc, byte| {
                (acc * 256 + u64::from(byte)) % u64::from(Q)
            });
        self.u64_to_element(value)
    }

    fn to_nat(&self, e: &Self::E) -> Self::N {
        assert!(e.coefficients[1..]
            .iter()
            .all(|&coefficient| coefficient == 0));
        RuntimeNat::from_u64(u64::from(e.coefficients[0]))
    }
}

impl SupportsSampling for RuntimeFp24Ext6 {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
        let mut coefficients = [0u32; EXTENSION_DEGREE];
        for coefficient in &mut coefficients {
            *coefficient = sample_base(&mut rng);
        }
        RuntimeElement::new(coefficients)
    }
}

/// Shared exact sampler for the prime coordinates, including the V1 codec.
pub(in crate::runtime) fn sample_base(mut rng: impl FnMut(usize) -> Vec<u8>) -> u32 {
    loop {
        let bytes = rng(3);
        assert_eq!(bytes.len(), 3);
        let candidate = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]) & 0x7f_ffff;
        if candidate < Q {
            return candidate;
        }
    }
}

impl InterpolationField<3> for RuntimeFp24Ext6 {
    fn poly_evaluation_point(&self, i: usize) -> Self::E {
        self.u64_to_element(i as u64)
    }

    fn newton_denominator(&self, _k: usize, i: usize) -> Self::E {
        self.u64_to_element(invert_base(i as u32) as u64)
    }
}
