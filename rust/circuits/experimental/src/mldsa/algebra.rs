// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Experimental algebra used by the ML-DSA circuits.
//!
//! The proof field is the sextic extension `F_q[x] / (x^6 - 7)`, where
//! `q = 8_380_417`. Compile-time and runtime fields deliberately use distinct element types even
//! though their arithmetic is defined by the same polynomial.

use std::marker::PhantomData;

use core_algebra::{AlgebraicField, BareField, SerializableField, SupportsU64Conversions};

pub const Q: u32 = 8_380_417;
pub const BETA: u32 = 7;
pub const EXTENSION_DEGREE: usize = 6;
pub const BASE_SERIALIZED_SIZE: usize = 3;
pub const SERIALIZED_SIZE: usize = BASE_SERIALIZED_SIZE * EXTENSION_DEGREE;

#[inline]
fn add_base(a: u32, b: u32) -> u32 {
    let sum = a + b;
    if sum >= Q {
        sum - Q
    } else {
        sum
    }
}

#[inline]
fn sub_base(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        a + Q - b
    }
}

#[inline]
fn mul_base(a: u32, b: u32) -> u32 {
    (u64::from(a) * u64::from(b) % u64::from(Q)) as u32
}

fn invert_base(value: u32) -> u32 {
    assert_ne!(value, 0, "cannot invert zero");
    // Binary extended GCD is materially faster here than exponentiation by
    // q-2. Keep the coefficients reduced in F_q, matching Fp24 in C++.
    let mut a = value;
    let mut b = Q;
    let mut u = 1;
    let mut v = 0;
    while a != 0 {
        if a & 1 == 0 {
            a >>= 1;
            u = half_base(u);
        } else {
            if a < b {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut u, &mut v);
            }
            a = (a - b) >> 1;
            u = half_base(sub_base(u, v));
        }
    }
    v
}

#[inline]
fn half_base(a: u32) -> u32 {
    if a & 1 == 0 {
        a >> 1
    } else {
        (a >> 1) + Q.div_ceil(2)
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

fn mul_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    let lhs = *a;
    if b[1..].iter().all(|&coefficient| coefficient == 0) {
        for (dst, &coefficient) in a.iter_mut().zip(&lhs) {
            *dst = mul_base(coefficient, b[0]);
        }
        return;
    }
    if lhs[1..].iter().all(|&coefficient| coefficient == 0) {
        for (dst, &coefficient) in a.iter_mut().zip(b) {
            *dst = mul_base(lhs[0], coefficient);
        }
        return;
    }
    let mut product = [0u64; 2 * EXTENSION_DEGREE - 1];
    for i in 0..EXTENSION_DEGREE {
        for j in 0..EXTENSION_DEGREE {
            product[i + j] += u64::from(lhs[i]) * u64::from(b[j]);
        }
    }
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

fn serialize(coefficients: &[u32; EXTENSION_DEGREE], dst: &mut [u8]) {
    assert_eq!(dst.len(), SERIALIZED_SIZE);
    for (coefficient, bytes) in coefficients
        .iter()
        .zip(dst.as_chunks_mut::<BASE_SERIALIZED_SIZE>().0.iter_mut())
    {
        bytes.copy_from_slice(&coefficient.to_le_bytes()[..BASE_SERIALIZED_SIZE]);
    }
}

fn deserialize(bytes: &[u8]) -> Result<[u32; EXTENSION_DEGREE], String> {
    if bytes.len() != SERIALIZED_SIZE {
        return Err(format!(
            "invalid ML-DSA extension element size: {}",
            bytes.len()
        ));
    }
    let mut coefficients = [0u32; EXTENSION_DEGREE];
    for (coefficient, chunk) in coefficients
        .iter_mut()
        .zip(bytes.as_chunks::<BASE_SERIALIZED_SIZE>().0.iter())
    {
        *coefficient = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], 0]);
        if *coefficient >= Q {
            return Err("non-canonical ML-DSA extension coefficient".to_owned());
        }
    }
    Ok(coefficients)
}

pub enum CompileTag {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompileElement {
    coefficients: [u32; EXTENSION_DEGREE],
    _tag: PhantomData<CompileTag>,
}

impl CompileElement {
    fn new(coefficients: [u32; EXTENSION_DEGREE]) -> Self {
        Self {
            coefficients,
            _tag: PhantomData,
        }
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

impl core_algebra::Comparable for CompileFp24Ext6 {
    fn compare(&self, a: &Self::E, b: &Self::E) -> std::cmp::Ordering {
        a.coefficients.cmp(&b.coefficients)
    }
}

impl SerializableField for CompileFp24Ext6 {
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

impl core_algebra::HasLookupPoints for CompileFp24Ext6 {
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

impl core_algebra::SupportsU128Conversions for CompileFp24Ext6 {
    fn u128_to_element(&self, n: u128) -> Self::E {
        assert!(n < u128::from(Q), "integer is not a canonical F_q element");
        self.u64_to_element(n as u64)
    }
}

impl compile_algebra::CompileField for CompileFp24Ext6 {
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

#[cfg(feature = "mldsa-runtime")]
mod runtime {
    use super::*;
    use core_algebra::Nat;
    use runtime_algebra::{
        field::{RuntimeSerializableField, SupportsSampling},
        poly::InterpolationField,
        RuntimeField, RuntimeNat, Subfield,
    };

    pub enum RuntimeTag {}

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct RuntimeElement {
        coefficients: [u32; EXTENSION_DEGREE],
        _tag: PhantomData<RuntimeTag>,
    }

    impl RuntimeElement {
        fn new(coefficients: [u32; EXTENSION_DEGREE]) -> Self {
            Self {
                coefficients,
                _tag: PhantomData,
            }
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

        #[must_use]
        pub fn from_compile(&self, element: &CompileElement) -> RuntimeElement {
            RuntimeElement::new(element.coefficients)
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

    impl core_algebra::HasLookupPoints for RuntimeFp24Ext6 {
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
            std::array::from_fn(|i| {
                u64::from_le_bytes(bytes[8 * i..8 * (i + 1)].try_into().unwrap())
            })
        }

        fn words64_to_element(&self, words: &[u64; 3]) -> Result<Self::E, String> {
            let mut bytes = [0u8; 24];
            for (word, chunk) in words.iter().zip(bytes.as_chunks_mut::<8>().0.iter_mut()) {
                chunk.copy_from_slice(&word.to_le_bytes());
            }
            if bytes[SERIALIZED_SIZE..].iter().any(|&byte| byte != 0) {
                return Err("non-canonical ML-DSA extension word padding".to_owned());
            }
            deserialize(&bytes[..SERIALIZED_SIZE]).map(RuntimeElement::new)
        }
    }

    impl core_algebra::SupportsNatConversions<3> for RuntimeFp24Ext6 {
        type N = RuntimeNat<3>;

        fn reduce_nat(&self, n: &Self::N) -> Self::E {
            let bytes: Vec<u8> = n
                .to_limbs()
                .iter()
                .flat_map(|word| word.to_le_bytes())
                .collect();
            let value = bytes.iter().rev().fold(0u64, |acc, &byte| {
                (acc * 256 + u64::from(byte)) % u64::from(Q)
            });
            self.u64_to_element(value)
        }

        fn to_nat(&self, e: &Self::E) -> Self::N {
            assert!(e.coefficients[1..]
                .iter()
                .all(|&coefficient| coefficient == 0));
            RuntimeNat::from_limbs(&[u64::from(e.coefficients[0]), 0, 0])
        }
    }

    impl SupportsSampling<3> for RuntimeFp24Ext6 {
        fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
            let mut coefficients = [0u32; EXTENSION_DEGREE];
            for coefficient in &mut coefficients {
                loop {
                    let bytes = rng(4);
                    assert_eq!(bytes.len(), 4);
                    let candidate = u32::from_le_bytes(bytes.try_into().unwrap()) & 0x7f_ffff;
                    if candidate < Q {
                        *coefficient = candidate;
                        break;
                    }
                }
            }
            RuntimeElement::new(coefficients)
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

    impl Subfield for RuntimeFp24Subfield {
        type E = RuntimeElement;

        fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
            assert_eq!(dst.len(), BASE_SERIALIZED_SIZE);
            assert!(self.contains(e), "element is not in the ML-DSA base field");
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
                return Err("invalid ML-DSA base-field element size".to_owned());
            }
            let value = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]);
            if value >= Q {
                return Err("non-canonical ML-DSA base-field element".to_owned());
            }
            let mut coefficients = [0; EXTENSION_DEGREE];
            coefficients[0] = value;
            Ok(RuntimeElement::new(coefficients))
        }

        fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
            loop {
                let bytes = rng(4);
                assert_eq!(bytes.len(), 4);
                let candidate = u32::from_le_bytes(bytes.try_into().unwrap()) & 0x7f_ffff;
                if candidate < Q {
                    let mut coefficients = [0; EXTENSION_DEGREE];
                    coefficients[0] = candidate;
                    return RuntimeElement::new(coefficients);
                }
            }
        }
    }
}

#[cfg(feature = "mldsa-runtime")]
pub use runtime::{RuntimeElement, RuntimeFp24Ext6, RuntimeFp24Subfield};
