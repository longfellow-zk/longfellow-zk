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

use std::ops::Range;

use super::{
    batch_inverse, difference, InterpolationPlan, RangeInterpolatorFactory, Ranges, RuntimeField,
};
use crate::core::algebra::{Nat, SupportsNatConversions, SupportsU64Conversions};

/// Scalar arithmetic interpolation for fields without a suitable FFT root.
/// `limit` is the exclusive point-table bound and cannot exceed the characteristic.
pub struct ScalarInterpolatorFactory<'a, const W: usize, F: RuntimeField<W>> {
    field: &'a F,
    limit: usize,
}

impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + SupportsNatConversions<W> + SupportsU64Conversions,
    > ScalarInterpolatorFactory<'a, W, F>
{
    pub fn new(field: &'a F, limit: usize) -> Self {
        assert!(
            !field.is_binary() && limit > 0 && u64::try_from(limit - 1).is_ok(),
            "invalid scalar point table"
        );
        assert!(
            F::N::from_u64((limit - 1) as u64) <= field.to_nat(&field.mone()),
            "point table exceeds characteristic"
        );
        Self { field, limit }
    }
}

/// Public reciprocal differences reused by scalar interpolations.
pub struct ScalarInterpolationPlan<'a, const W: usize, F: RuntimeField<W>> {
    field: &'a F,
    ranges: Ranges,
    inverses: Vec<F::E>,
}

impl<const W: usize, F: RuntimeField<W> + SupportsU64Conversions> InterpolationPlan<W, F>
    for ScalarInterpolationPlan<'_, W, F>
{
    fn apply(&self, source: &[F::E]) -> Vec<F::E> {
        let mut destination = vec![self.field.zero(); self.ranges.destination.len()];
        if self.ranges.trivial(source, &mut destination) {
            return destination;
        }
        let coefficients = self.newton_coefficients(source);
        for segment in self.ranges.outside() {
            for j in segment {
                destination[j - self.ranges.destination.start] = self.evaluate(&coefficients, j);
            }
        }
        destination
    }
}

impl<const W: usize, F: RuntimeField<W> + SupportsU64Conversions>
    ScalarInterpolationPlan<'_, W, F>
{
    /// Convert samples to Newton coefficients using precomputed inverse differences.
    fn newton_coefficients(&self, source: &[F::E]) -> Vec<F::E> {
        let mut coefficients = source.to_vec();
        for order in 1..source.len() {
            for i in (order..source.len()).rev() {
                coefficients[i] = self.field.mulf(
                    &self.field.subf(&coefficients[i], &coefficients[i - 1]),
                    &self.inverses[order - 1],
                );
            }
        }
        coefficients
    }

    /// Evaluate the Newton form at one arithmetic-table point by Horner's rule.
    fn evaluate(&self, coefficients: &[F::E], index: usize) -> F::E {
        let mut value = coefficients.last().unwrap().clone();
        for i in (0..coefficients.len() - 1).rev() {
            let mut next = coefficients[i].clone();
            self.field.fma(
                &mut next,
                &value,
                &difference(index, self.ranges.source.start + i, self.field),
            );
            value = next;
        }
        value
    }
}

impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + SupportsNatConversions<W> + SupportsU64Conversions,
    > RangeInterpolatorFactory<W, F> for ScalarInterpolatorFactory<'a, W, F>
{
    type Plan = ScalarInterpolationPlan<'a, W, F>;
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool {
        Ranges::valid(&source, &destination, self.limit)
    }
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "unsupported scalar interpolation ranges"
        );
        let ranges = Ranges::new(source, destination);
        let differences: Vec<_> = if ranges.needs_work() {
            (1..ranges.source.len())
                .map(|i| self.field.u64_to_element(i as u64))
                .collect()
        } else {
            Vec::new()
        };
        let inverses = batch_inverse(&differences, self.field);
        ScalarInterpolationPlan {
            field: self.field,
            ranges,
            inverses,
        }
    }
    fn point(&self, index: usize) -> F::E {
        assert!(index < self.limit, "point outside scalar domain");
        self.field.u64_to_element(index as u64)
    }
}

impl<const W: usize, F> crate::runtime::algebra::EvaluationDomain<W, F>
    for ScalarInterpolatorFactory<'_, W, F>
where F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + SupportsU64Conversions
        + SupportsNatConversions<W>
{
    fn field(&self) -> &F {
        self.field
    }
    fn domain_id(&self) -> Vec<u8> {
        super::arithmetic::evaluation_domain_id(self.field)
    }
}
