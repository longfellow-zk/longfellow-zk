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

use crate::runtime::algebra::gf2_128::Gf2_128;

pub trait SubfieldV1 {
    type E;
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]);
    #[inline]
    fn to_bytes(&self, e: &Self::E) -> Vec<u8> {
        let len = self.serialized_size_bytes();
        let mut buf = vec![0u8; len];
        self.to_bytes_into(e, &mut buf);
        buf
    }
    fn contains(&self, e: &Self::E) -> bool;
    fn serialized_size_bytes(&self) -> usize;
    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String>;
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, rng: R) -> Self::E;
}

/// V1-only compact-row interpolation; ordinary plans do not require this capability.
pub trait InterpolationPlanV1<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>:
    crate::runtime::algebra::range_interpolation::InterpolationPlan<W, F>
{
    /// A public layout hint that all source values belong to `subfield`.
    /// The default implementation works without subfield specialization.
    fn apply_subfield_v1<SF: SubfieldV1<E = F::E>>(
        &self,
        source: &[F::E],
        _subfield: &SF,
    ) -> Vec<F::E> {
        self.apply(source)
    }
}

impl<const W: usize, F: crate::runtime::algebra::RuntimeBinaryField<W, E = Gf2_128>>
    InterpolationPlanV1<W, F>
    for crate::runtime::algebra::range_interpolation::binary::BinaryInterpolationPlan<'_, W, F>
{
}
impl<
        const W: usize,
        F: crate::runtime::algebra::RuntimeField<W> + crate::core::algebra::SupportsU64Conversions,
    > InterpolationPlanV1<W, F>
    for crate::runtime::algebra::range_interpolation::scalar::ScalarInterpolationPlan<'_, W, F>
{
}
impl<
        const W: usize,
        F: crate::runtime::algebra::SupportsQuadraticExtension<W>
            + crate::core::algebra::SupportsU64Conversions,
    > InterpolationPlanV1<W, F>
    for crate::runtime::algebra::range_interpolation::quadratic_extension_fft::QuadraticExtensionFftInterpolationPlan<
        '_,
        W,
        F,
    >
{
}
