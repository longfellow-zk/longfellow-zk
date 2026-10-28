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

//! Interpolate between contiguous ranges of a fixed, implicit point table.
//!
//! A source of length `k > 0` specifies the unique polynomial of degree `< k`.
//! Destination ranges may precede, follow, or overlap the source, and may have
//! any length, including zero. Ranges describe point indices, not memory aliases.
//! Plans contain public preprocessing only and may be reused for different rows.
//! Each application returns its encoded vector and allocates temporary work locally.

//!
//! ```
//! use longfellow_zk::runtime::algebra::{
//!     fp2::Fp2Field, p256::P256Field, range_interpolation::QuadraticExtensionFftInterpolatorFactory,
//!     InterpolationPlan, RangeInterpolatorFactory, SupportsFFT,
//! };
//! use longfellow_zk::core::algebra::AlgebraicField;
//!
//! let field = P256Field::new();
//! let extension = Fp2Field::new(&field);
//! let domain = QuadraticExtensionFftInterpolatorFactory::new(
//!     &field, &extension, extension.omega(), extension.omega_order(),
//! );
//! let plan = domain.make_range(5..8, 0..12);
//! let output = plan.apply(&vec![field.one(); 3]);
//! assert_eq!(output, vec![field.one(); 12]);
//! ```

use std::ops::Range;

use super::RuntimeField;
use crate::core::algebra::{AlgebraicField, SupportsU64Conversions};

mod arithmetic;
mod binary;
#[cfg(feature = "experimental")]
mod crt;
#[cfg(feature = "experimental")]
mod crt_fft;
mod quadratic_extension_fft;
mod scalar;
pub use binary::BinaryInterpolatorFactory;
#[cfg(feature = "experimental")]
pub use crt::CrtInterpolatorFactory;
pub use quadratic_extension_fft::QuadraticExtensionFftInterpolatorFactory;
pub use scalar::ScalarInterpolatorFactory;

/// An immutable plan for fixed source and destination ranges.
pub trait InterpolationPlan<const W: usize, F: RuntimeField<W>> {
    /// Return evaluations on the destination range used to construct the plan.
    /// The source length must match the plan; its values are unchanged.
    fn apply(&self, source: &[F::E]) -> Vec<F::E>;
}

/// A backend and its fixed ordering of distinct evaluation points.
///
/// Arithmetic backends use `point(i) = i`; binary backends use the supplied
/// additive basis. Factories and plans are independent of either proof protocol.
pub trait RangeInterpolatorFactory<const W: usize, F: RuntimeField<W>> {
    type Plan: InterpolationPlan<W, F>;

    /// Whether both ranges fit the distinct point table and backend capacity.
    /// Empty or reversed source ranges and reversed destinations are rejected.
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool;

    /// Panics if `can_interpolate` is false.
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan;

    /// Panics if the index is outside the distinct point table.
    fn point(&self, index: usize) -> F::E;
}

impl<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F> + ?Sized>
    RangeInterpolatorFactory<W, F> for &D
{
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
pub trait EvaluationDomain<const W: usize, F: RuntimeField<W>>:
    RangeInterpolatorFactory<W, F>
{
    fn domain_id(&self) -> Vec<u8>;
}

impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F> + ?Sized> EvaluationDomain<W, F>
    for &D
{
    fn domain_id(&self) -> Vec<u8> {
        (**self).domain_id()
    }
}

/// Construct and apply one plan. Reuse a plan when interpolating many rows.
/// Panics on index overflow or unsupported ranges.
pub fn interpolate_range<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
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

struct Ranges {
    source: Range<usize>,
    destination: Range<usize>,
}

impl Ranges {
    fn valid(source: &Range<usize>, destination: &Range<usize>, limit: usize) -> bool {
        source.start < source.end
            && source.end <= limit
            && destination.start <= destination.end
            && destination.end <= limit
    }

    fn new(source: Range<usize>, destination: Range<usize>) -> Self {
        Self {
            source,
            destination,
        }
    }

    /// At most two nonoverlapping destination segments, in destination order.
    fn outside(&self) -> Vec<Range<usize>> {
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

    fn trivial<E: Clone>(&self, source: &[E], destination: &mut [E]) -> bool {
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

    fn needs_work(&self) -> bool {
        self.source.len() > 1 && !self.outside().is_empty()
    }
}

pub(super) use super::field::batch_inverse;

/// Convert a signed index difference without signed integer casts or overflow.
fn difference<F: AlgebraicField + SupportsU64Conversions>(a: usize, b: usize, f: &F) -> F::E {
    if a >= b {
        f.u64_to_element((a - b) as u64)
    } else {
        f.neg(&f.u64_to_element((b - a) as u64))
    }
}
