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

//! The interpolation traits and the range bookkeeping every backend shares.

use std::ops::Range;

use crate::{
    core::algebra::{AlgebraicField, SupportsU64Conversions},
    runtime::algebra::RuntimeField,
};

/// An immutable plan for fixed source and destination ranges.
pub trait InterpolationPlan<F: RuntimeField> {
    /// Return evaluations on the destination range used to construct the plan.
    /// The source length must match the plan; its values are unchanged.
    fn apply(&self, source: &[F::E]) -> Vec<F::E>;
}

/// A backend and its fixed ordering of distinct evaluation points.
///
/// Arithmetic backends use `point(i) = i`; binary backends use the supplied
/// additive basis. Factories and plans are independent of either proof protocol.
pub trait RangeInterpolatorFactory<F: RuntimeField> {
    type Plan: InterpolationPlan<F>;

    /// Whether both ranges fit the distinct point table and backend capacity.
    /// Empty or reversed source ranges and reversed destinations are rejected.
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool;

    /// Panics if `can_interpolate` is false.
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan;

    /// Panics if the index is outside the distinct point table.
    fn point(&self, index: usize) -> F::E;
}

impl<F: RuntimeField, D: RangeInterpolatorFactory<F> + ?Sized> RangeInterpolatorFactory<F> for &D {
    type Plan = D::Plan;
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool {
        (**self).can_interpolate(source, destination)
    }
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan {
        (**self).make_range(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        (**self).point(index)
    }
}

/// Stable identity of the field and fixed point ordering, independent of the
/// interpolation algorithm. This metadata introduces no evaluation points.
pub trait EvaluationDomain<F: RuntimeField>: RangeInterpolatorFactory<F> {
    /// The arithmetic instance used by this domain's interpolation plans.
    /// Protocol callers derive their field from here, so runtime-configured
    /// moduli cannot accidentally disagree between interpolation and checks.
    fn field(&self) -> &F;
    fn domain_id(&self) -> Vec<u8>;
}

impl<F: RuntimeField, D: EvaluationDomain<F> + ?Sized> EvaluationDomain<F> for &D {
    fn field(&self) -> &F {
        (**self).field()
    }
    fn domain_id(&self) -> Vec<u8> {
        (**self).domain_id()
    }
}

/// Construct and apply one plan. Reuse a plan when interpolating many rows.
/// Panics on index overflow or unsupported ranges.
pub fn interpolate_range<F: RuntimeField, D: RangeInterpolatorFactory<F>>(
    source_begin: usize,
    values: &[F::E],
    destination: Range<usize>,
    domain: &D,
) -> Vec<F::E> {
    let end = source_begin
        .checked_add(values.len())
        .expect("source range overflow");
    domain
        .make_range(source_begin..end, destination)
        .apply(values)
}

pub(super) struct Ranges {
    pub(super) source: Range<usize>,
    pub(super) destination: Range<usize>,
}

impl Ranges {
    pub(super) fn valid(source: &Range<usize>, destination: &Range<usize>, limit: usize) -> bool {
        source.start < source.end
            && source.end <= limit
            && destination.start <= destination.end
            && destination.end <= limit
    }

    pub(super) fn new(source: Range<usize>, destination: Range<usize>) -> Self {
        Self {
            source,
            destination,
        }
    }

    /// At most two nonoverlapping destination segments, in destination order.
    pub(super) fn outside(&self) -> Vec<Range<usize>> {
        let mut out = Vec::new();
        let before = self.destination.start..self.destination.end.min(self.source.start);
        if !before.is_empty() {
            out.push(before);
        }
        let after = self.destination.start.max(self.source.end)..self.destination.end;
        if !after.is_empty() {
            out.push(after);
        }
        out
    }

    fn copy_overlap<E: Clone>(&self, source: &[E], destination: &mut [E]) {
        let begin = self.source.start.max(self.destination.start);
        let end = self.source.end.min(self.destination.end);
        if begin < end {
            destination[begin - self.destination.start..end - self.destination.start]
                .clone_from_slice(&source[begin - self.source.start..end - self.source.start]);
        }
    }

    pub(super) fn trivial<E: Clone>(&self, source: &[E], destination: &mut [E]) -> bool {
        assert_eq!(source.len(), self.source.len(), "wrong source length");
        if destination.is_empty() {
            return true;
        }
        if source.len() == 1 {
            destination.fill(source[0].clone());
            return true;
        }
        self.copy_overlap(source, destination);
        self.destination.start >= self.source.start && self.destination.end <= self.source.end
    }

    pub(super) fn needs_work(&self) -> bool {
        self.source.len() > 1 && !self.outside().is_empty()
    }
}

/// Convert a signed index difference without signed integer casts or overflow.
pub(super) fn difference<F: AlgebraicField + SupportsU64Conversions>(
    a: usize,
    b: usize,
    f: &F,
) -> F::E {
    if a >= b {
        f.u64_to_element((a - b) as u64)
    } else {
        f.neg(&f.u64_to_element((b - a) as u64))
    }
}
