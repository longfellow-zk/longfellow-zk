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
        RuntimeField, RuntimeNat, SubfieldV1,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RuntimeElement {
    coefficients: [u32; EXTENSION_DEGREE],
}

impl RuntimeElement {
    fn new(coefficients: [u32; EXTENSION_DEGREE]) -> Self {
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
    type Accum = RuntimeElement;

    fn zero_accum(&self) -> Self::Accum {
        self.zero()
    }

    fn mac(&self, acc: &mut Self::Accum, x: &Self::E, y: &Self::E) {
        let product = self.mulf(x, y);
        self.add(acc, &product);
    }

    fn accum_reduce(&self, acc: &Self::Accum) -> Self::E {
        *acc
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
pub(super) fn sample_base(mut rng: impl FnMut(usize) -> Vec<u8>) -> u32 {
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

pub struct RuntimeFp24Subfield;

impl SubfieldV1 for RuntimeFp24Subfield {
    type E = RuntimeElement;

    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(dst.len(), BASE_SERIALIZED_SIZE);
        assert!(self.contains(e), "element is not in the Fp24 base field");
        dst.copy_from_slice(&e.coefficients[0].to_le_bytes()[..BASE_SERIALIZED_SIZE]);
    }

    fn contains(&self, e: &Self::E) -> bool {
        e.coefficients[1..]
            .iter()
            .all(|&coefficient| coefficient == 0)
    }

    fn serialized_size_bytes(&self) -> usize {
        BASE_SERIALIZED_SIZE
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        if bytes.len() != BASE_SERIALIZED_SIZE {
            return Err("invalid Fp24 base-field element size".to_owned());
        }
        let value = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]);
        if value >= Q {
            return Err("non-canonical Fp24 base-field element".to_owned());
        }
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = value;
        Ok(RuntimeElement::new(coefficients))
    }

    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = sample_base(&mut rng);
        RuntimeElement::new(coefficients)
    }
}
