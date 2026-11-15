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

use crate::{
    core::algebra::{
        fp24::{BETA, EXTENSION_DEGREE, Q, SERIALIZED_SIZE},
        AlgebraicField, BareField, FieldID, HasLookupPoints, Nat, RegisteredField, Sealed,
        SerializableField, SupportsNatConversions, SupportsU64Conversions,
    },
    runtime::algebra::{
        InterpolationField, RuntimeField, RuntimeNat, RuntimeSerializableField, SupportsSampling,
    },
};
mod base;
pub use base::{add_base, invert_base, mul_base, sub_base};

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

impl Sealed for RuntimeFp24Ext6 {}
impl RegisteredField for RuntimeFp24Ext6 {
    const ID: FieldID = FieldID::Fp24Ext6;
    const BYTES: usize = SERIALIZED_SIZE;
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

impl HasLookupPoints for RuntimeFp24Ext6 {
    fn lookup_point(&self, n: usize, i: usize) -> Self::E {
        let value =
            ((2 * i) as u64 + u64::from(Q) - ((n - 1) as u64 % u64::from(Q))) % u64::from(Q);
        self.u64_to_element(value)
    }
}

impl RuntimeField for RuntimeFp24Ext6 {
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
        let product = product_unreduced(&x.coefficients, &y.coefficients);
        for (coefficient, term) in acc.iter_mut().zip(product) {
            *coefficient += u128::from(term);
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

impl SupportsNatConversions<3> for RuntimeFp24Ext6 {
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
    fn sample<R: FnMut(&mut [u8])>(&self, mut rng: R) -> Self::E {
        let mut coefficients = [0u32; EXTENSION_DEGREE];
        for coefficient in &mut coefficients {
            *coefficient = sample_base(&mut rng);
        }
        RuntimeElement::new(coefficients)
    }
}

/// Shared exact sampler for the prime coordinates, including the V1 codec.
pub fn sample_base(mut rng: impl FnMut(&mut [u8])) -> u32 {
    loop {
        let mut bytes = [0; 3];
        rng(&mut bytes);
        let candidate = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]) & 0x7f_ffff;
        if candidate < Q {
            return candidate;
        }
    }
}

impl InterpolationField for RuntimeFp24Ext6 {
    fn poly_evaluation_point(&self, i: usize) -> Self::E {
        self.u64_to_element(i as u64)
    }

    fn newton_denominator(&self, _k: usize, i: usize) -> Self::E {
        self.u64_to_element(invert_base(i as u32) as u64)
    }
}

fn add_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    for i in 0..EXTENSION_DEGREE {
        a[i] = add_base(a[i], b[i]);
    }
}

fn sub_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    for i in 0..EXTENSION_DEGREE {
        a[i] = sub_base(a[i], b[i]);
    }
}

#[inline]
fn product_unreduced(
    a: &[u32; EXTENSION_DEGREE],
    b: &[u32; EXTENSION_DEGREE],
) -> [u64; 2 * EXTENSION_DEGREE - 1] {
    let mut product = [0u64; 2 * EXTENSION_DEGREE - 1];
    for i in 0..EXTENSION_DEGREE {
        for j in 0..EXTENSION_DEGREE {
            product[i + j] += u64::from(a[i]) * u64::from(b[j]);
        }
    }
    product
}

fn mul_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    let mut product = product_unreduced(a, b);
    for i in 0..(EXTENSION_DEGREE - 1) {
        product[i] += product[i + EXTENSION_DEGREE] * u64::from(BETA);
    }
    for i in 0..EXTENSION_DEGREE {
        a[i] = (product[i] % u64::from(Q)) as u32;
    }
}

fn invert_extension(a: &[u32; EXTENSION_DEGREE]) -> [u32; EXTENSION_DEGREE] {
    assert!(
        a.iter().any(|&coefficient| coefficient != 0),
        "cannot invert zero"
    );

    if a[1..].iter().all(|&coefficient| coefficient == 0) {
        let mut result = [0; EXTENSION_DEGREE];
        result[0] = invert_base(a[0]);
        return result;
    }

    // Multiplication by `a` is a beta-circulant matrix. Solve a*x = 1 over F_q.
    let mut matrix = [[0u32; EXTENSION_DEGREE]; EXTENSION_DEGREE];
    for row in 0..EXTENSION_DEGREE {
        for column in 0..EXTENSION_DEGREE {
            matrix[row][column] = if row >= column {
                a[row - column]
            } else {
                mul_base(a[row + EXTENSION_DEGREE - column], BETA)
            };
        }
    }
    let mut result = [0u32; EXTENSION_DEGREE];
    result[0] = 1;

    for column in 0..EXTENSION_DEGREE {
        let pivot = (column..EXTENSION_DEGREE)
            .find(|&row| matrix[row][column] != 0)
            .expect("extension polynomial must define a field");
        if pivot != column {
            matrix.swap(column, pivot);
            result.swap(column, pivot);
        }

        let scale = invert_base(matrix[column][column]);
        for entry in &mut matrix[column][column..] {
            *entry = mul_base(*entry, scale);
        }
        result[column] = mul_base(result[column], scale);

        let pivot_row = matrix[column];
        let pivot_result = result[column];
        for row in 0..EXTENSION_DEGREE {
            if row == column {
                continue;
            }
            let factor = matrix[row][column];
            for (j, entry) in matrix[row].iter_mut().enumerate().skip(column) {
                *entry = sub_base(*entry, mul_base(factor, pivot_row[j]));
            }
            result[row] = sub_base(result[row], mul_base(factor, pivot_result));
        }
    }
    result
}

fn serialize(coefficients: &[u32; EXTENSION_DEGREE], out: &mut [u8]) {
    assert_eq!(out.len(), SERIALIZED_SIZE);
    for i in 0..EXTENSION_DEGREE {
        let x = coefficients[i];
        out[3 * i] = x as u8;
        out[3 * i + 1] = (x >> 8) as u8;
        out[3 * i + 2] = (x >> 16) as u8;
    }
}
fn deserialize(bytes: &[u8]) -> Result<[u32; EXTENSION_DEGREE], String> {
    if bytes.len() != SERIALIZED_SIZE {
        return Err("invalid Fp24 sextic extension element size".into());
    }
    let mut result = [0; EXTENSION_DEGREE];
    for i in 0..EXTENSION_DEGREE {
        let x = u32::from(bytes[3 * i])
            | u32::from(bytes[3 * i + 1]) << 8
            | u32::from(bytes[3 * i + 2]) << 16;
        if x >= Q {
            return Err("non-canonical Fp24 sextic extension coefficient".into());
        }
        result[i] = x;
    }
    Ok(result)
}
#[cfg(test)]
mod tests;
