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

pub use crate::core::algebra::AlgebraicField;

pub trait RuntimeSerializableField<const W: usize>:
    RuntimeField<W> + crate::core::algebra::SerializableField
{
    fn to_words64(&self, e: &Self::E) -> [u64; W];
    fn words64_to_element(&self, words: &[u64; W]) -> Result<Self::E, String>;
}

pub trait RuntimeField<const W: usize>: SupportsSampling {
    type Accum: Clone + std::fmt::Debug;

    // Arithmetic operations

    /// Raise an element to a nonnegative public exponent by repeated squaring.
    fn pow(&self, value: &Self::E, mut exponent: usize) -> Self::E {
        let mut base = value.clone();
        let mut result = self.one();
        while exponent != 0 {
            if exponent & 1 != 0 {
                self.mul(&mut result, &base);
            }
            base = self.mulf(&base, &base);
            exponent >>= 1;
        }
        result
    }

    #[inline]
    fn fma(&self, e1: &mut Self::E, a: &Self::E, b: &Self::E) {
        let mut prod = a.clone();
        self.mul(&mut prod, b);
        self.add(e1, &prod);
    }

    #[inline]
    fn fnms(&self, e1: &mut Self::E, a: &Self::E, b: &Self::E) {
        let mut prod = a.clone();
        self.mul(&mut prod, b);
        self.sub(e1, &prod);
    }

    fn zero_accum(&self) -> Self::Accum;
    fn mac(&self, acc: &mut Self::Accum, x: &Self::E, y: &Self::E);
    fn accum_reduce(&self, acc: &Self::Accum) -> Self::E;
}

pub use crate::core::algebra::{
    SupportsNatConversions, SupportsU128Conversions, SupportsU64Conversions,
};

/// Sample with minimum byte draws, mask unused high bits, and reject overflow.
/// Sampling is independent of storage width and serialization.
pub trait SupportsSampling: AlgebraicField {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, rng: R) -> Self::E;
}

pub trait RuntimeBinaryField<const W: usize>: RuntimeField<W> {}

/// Marker for base fields that support [`crate::runtime::algebra::fp2::Fp2Field`].
///
/// `Fp2Field` uses the fixed polynomial `x^2 + 1`, so implementors must ensure
/// that `-1` is not a square in the base field. This property depends on the
/// concrete modulus and cannot be inferred from a generic prime-field type.
pub trait SupportsQuadraticExtension<const W: usize>: RuntimeField<W> {}

pub trait SupportsFFT<const W: usize>: RuntimeField<W> {
    fn omega(&self) -> Self::E;
    fn omega_order(&self) -> u64;
}

/// Invert nonzero elements using one inversion. Empty input is valid.
pub(crate) fn batch_inverse<F: AlgebraicField>(values: &[F::E], field: &F) -> Vec<F::E> {
    let mut products = Vec::with_capacity(values.len());
    let mut product = field.one();
    for value in values {
        assert!(!field.is_zero(value), "batch inversion of zero");
        products.push(product.clone());
        field.mul(&mut product, value);
    }
    if values.is_empty() {
        return products;
    }
    let mut inverse = field.invert(&product);
    for i in (0..values.len()).rev() {
        let prefix = products[i].clone();
        products[i] = field.mulf(&inverse, &prefix);
        field.mul(&mut inverse, &values[i]);
    }
    products
}
