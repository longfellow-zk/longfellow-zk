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

//! Range interpolation in the normalized novel basis used by LCH14.
//!
//! A mixed transform knows a contiguous interval of evaluations and the high
//! coefficient suffix. Prefixes and suffixes use the ordinary bidirectional
//! FFT. An interval contained in one half first folds the known coefficients
//! into that half. A crossing interval fits its left samples, then repairs the
//! right samples with one vanishing-polynomial multiple. Thus recursion reaches
//! at most one crossing merge. All transforms operate on dense arrays.

use std::ops::Range;

use super::{batch_inverse, InterpolationPlan, RangeInterpolatorFactory, Ranges};
use crate::runtime::algebra::{
    blas, field::RuntimeBinaryField, gf2_128::Gf2_128, lch14::Lch14, subfield_v1::BinarySubfield,
};

/// Additive point-table interpolation over a fixed binary basis.
/// The enclosing source coset determines the transform size, which can be much
/// larger than the sample count near a high dyadic boundary.
pub struct BinaryInterpolatorFactory<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> {
    field: &'a F,
    subfield: &'a BinarySubfield,
}

impl<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>
    BinaryInterpolatorFactory<'a, W, F>
{
    pub fn new(field: &'a F, subfield: &'a BinarySubfield) -> Self {
        Self { field, subfield }
    }
}

/// Complete coefficient and evaluation vectors, both in the original ordering.
struct MixedResult {
    coefficients: Vec<Gf2_128>,
    evaluations: Vec<Gf2_128>,
}

/// Each nonordinary step either descends into one half or performs the sole merge.
enum Operation {
    Ordinary,
    Contained(Box<BinaryTransform>),
    Crossing(CrossingMerge),
}

/// Public preprocessing for a mixed transform of size `2^log`.
/// Evaluations occupy `[start, start + count)` on points `coset XOR i`;
/// the supplied coefficient suffix occupies `[count, 2^log)` in the novel basis.
struct BinaryTransform {
    log: usize,
    coset: usize,
    start: usize,
    count: usize,
    operation: Operation,
}

impl BinaryTransform {
    /// Choose an ordinary transform, a contained subproblem, or a crossing merge.
    fn new<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        size: usize,
        coset: usize,
        start: usize,
        count: usize,
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> Self {
        debug_assert!(size.is_power_of_two());
        debug_assert!(start + count <= size);
        let log = size.trailing_zeros() as usize;
        // Prefixes (start == 0) and suffixes (start + count == size) go
        // directly to the ordinary bidirectional FFT, without a merge or
        // vanishing-polynomial preprocessing. With no samples, it is a forward FFT.
        let operation = if count == 0 || start == 0 || start + count == size {
            Operation::Ordinary
        } else {
            let half = size / 2;
            if start + count <= half || start >= half {
                let offset = if start >= half { half } else { 0 };
                Operation::Contained(Box::new(Self::new(
                    half,
                    coset ^ offset,
                    start - offset,
                    count,
                    fft,
                    field,
                )))
            } else {
                Operation::Crossing(CrossingMerge::new(log, coset, start, count, fft, field))
            }
        };
        Self {
            log,
            coset,
            start,
            count,
            operation,
        }
    }

    fn size(&self) -> usize {
        1 << self.log
    }

    /// Apply a prefix or suffix mixed FFT and reassemble the full vectors.
    /// LCH14 handles suffix ordering and returns coefficients in the same novel basis.
    fn ordinary<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        log: usize,
        coset: usize,
        start: usize,
        samples: &[Gf2_128],
        tail: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
    ) -> MixedResult {
        let count = samples.len();
        assert!(count == 0 || start == 0 || start + count == 1 << log);
        let suffix = start != 0 && count != 0;
        let mut mixed = samples.to_vec();
        mixed.extend_from_slice(tail);
        if suffix {
            fft.bidirectional_fft_suffix_on_coset(log, coset, count, &mut mixed);
        } else {
            fft.bidirectional_fft_on_coset(log, coset, count, &mut mixed);
        }
        let mut coefficients = mixed[..count].to_vec();
        coefficients.extend_from_slice(tail);
        mixed[..count].copy_from_slice(samples);
        if suffix {
            // The suffix FFT returns missing prefix values after the coefficients.
            mixed.rotate_left(count);
        }
        MixedResult {
            coefficients,
            evaluations: mixed,
        }
    }

    /// Recover all coefficients and evaluations, preserving the supplied suffix.
    fn apply<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        samples: &[Gf2_128],
        tail: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        debug_assert_eq!(samples.len(), self.count);
        debug_assert_eq!(samples.len() + tail.len(), self.size());
        match &self.operation {
            Operation::Ordinary => {
                Self::ordinary(self.log, self.coset, self.start, samples, tail, fft)
            }
            Operation::Contained(child) => self.apply_contained(child, samples, tail, fft, field),
            Operation::Crossing(merge) => self.apply_crossing(merge, samples, tail, fft, field),
        }
    }

    /// In one occupied half, P = A + X_half B restricts to U = A + c B.
    /// All coefficients of B are known, so recurse only to recover U.
    fn apply_contained<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        child: &Self,
        samples: &[Gf2_128],
        tail: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        let half = self.size() / 2;
        let offset = if self.start >= half { half } else { 0 };
        let upper = &tail[half - self.count..];
        let twiddle = fft.twiddle(self.log - 1, self.coset ^ offset);
        let folded = fold_coefficients(
            &tail[..half - self.count],
            &upper[self.count..],
            &twiddle,
            field,
        );
        let result = child.apply(samples, &folded, fft, field);
        self.complete_half(result, upper, offset, fft, field)
    }

    /// Recover A = U + c B and evaluate the other half, where the restriction
    /// is U + B. The stored evaluations are returned in left-then-right order.
    fn complete_half<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        result: MixedResult,
        upper: &[Gf2_128],
        offset: usize,
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        let half = self.size() / 2;
        let twiddle = fft.twiddle(self.log - 1, self.coset ^ offset);
        let mut coefficients = fold_coefficients(&result.coefficients, upper, &twiddle, field);
        coefficients.extend_from_slice(upper);
        let mut opposite = result.coefficients;
        blas::add(&mut opposite, upper, field);
        fft.fft(self.log - 1, self.coset ^ offset ^ half, &mut opposite);
        let evaluations = if offset == 0 {
            [result.evaluations, opposite].concat()
        } else {
            [opposite, result.evaluations].concat()
        };
        MixedResult {
            coefficients,
            evaluations,
        }
    }

    /// First fit the left suffix, then repair the right prefix. The correction
    /// vanishes on every left sample and has degree less than the sample count.
    fn apply_crossing<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        merge: &CrossingMerge,
        samples: &[Gf2_128],
        tail: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        let half = self.size() / 2;
        let left = half - self.start;
        let baseline = self.left_baseline(&samples[..left], tail, fft, field);
        let correction = merge.correction(
            self.log,
            self.coset,
            &samples[left..],
            &baseline.evaluations[half..],
            fft,
            field,
        );
        self.add_correction(baseline, correction, fft, field)
    }

    /// Temporarily set unknown coefficients from `left` to `count` to zero,
    /// retain the known high suffix, and solve only the left sample constraints.
    fn left_baseline<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        left_samples: &[Gf2_128],
        tail: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        let half = self.size() / 2;
        let left = left_samples.len();
        let mut provisional = vec![field.zero(); self.size()];
        provisional[self.count..].copy_from_slice(tail);
        let upper = &provisional[half..];
        let twiddle = fft.twiddle(self.log - 1, self.coset);
        let folded = fold_coefficients(&provisional[left..half], &upper[left..], &twiddle, field);
        let result = Self::ordinary(
            self.log - 1,
            self.coset,
            self.start,
            left_samples,
            &folded,
            fft,
        );
        self.complete_half(result, upper, 0, fft, field)
    }

    /// A short inverse FFT recovers the correction's novel coefficients.
    /// Its degree is below `count`, so the known coefficient suffix is unchanged.
    fn add_correction<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        mut baseline: MixedResult,
        correction: Vec<Gf2_128>,
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> MixedResult {
        let size = self.count.next_power_of_two();
        let mut coefficients = correction[..size].to_vec();
        fft.ifft(
            size.trailing_zeros() as usize,
            self.coset,
            &mut coefficients,
        );
        blas::add(
            &mut baseline.coefficients[..self.count],
            &coefficients[..self.count],
            field,
        );
        blas::add(&mut baseline.evaluations, &correction, field);
        baseline
    }
}

/// Form the novel coefficient vector `lower + twiddle * upper`.
fn fold_coefficients<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
    lower: &[Gf2_128],
    upper: &[Gf2_128],
    twiddle: &Gf2_128,
    field: &F,
) -> Vec<Gf2_128> {
    let mut folded = lower.to_vec();
    blas::axpy(&mut folded, twiddle, upper, field);
    folded
}

/// Values of Z_left on both halves, and its reciprocals at the right samples.
/// This public preprocessing is independent of row values and computed once.
struct CrossingMerge {
    vanishing: Vec<Gf2_128>,
    inverse_right: Vec<Gf2_128>,
}

impl CrossingMerge {
    /// Construct Z_left with a suffix bidirectional FFT: all left samples are
    /// zero, its leading novel coefficient is one, and higher coefficients zero.
    fn new<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        log: usize,
        coset: usize,
        start: usize,
        count: usize,
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> Self {
        let half = 1 << (log - 1);
        let left = half - start;
        let right = count - left;
        let mut tail = vec![field.zero(); half - left];
        tail[0] = field.one();
        let result =
            BinaryTransform::ordinary(log - 1, coset, start, &vec![field.zero(); left], &tail, fft);
        let mut vanishing = result.evaluations;
        let mut right_values = result.coefficients;
        fft.fft(log - 1, coset ^ half, &mut right_values);
        let inverse_right = batch_inverse(&right_values[..right], field);
        vanishing.extend(right_values);
        Self {
            vanishing,
            inverse_right,
        }
    }

    /// Interpolate q = (samples - baseline) / Z_left on the right prefix,
    /// extend q to both halves, and return the dense correction Z_left * q.
    /// Since deg(q) < right and deg(Z_left) = left, deg(correction) < count.
    fn correction<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>>(
        &self,
        log: usize,
        coset: usize,
        samples: &[Gf2_128],
        baseline: &[Gf2_128],
        fft: &Lch14<'_, W, F>,
        field: &F,
    ) -> Vec<Gf2_128> {
        let half = 1 << (log - 1);
        let mut quotient_samples = samples.to_vec();
        blas::sub(&mut quotient_samples, &baseline[..samples.len()], field);
        blas::mul(&mut quotient_samples, &self.inverse_right, field);
        let quotient = BinaryTransform::ordinary(
            log - 1,
            coset ^ half,
            0,
            &quotient_samples,
            &vec![field.zero(); half - samples.len()],
            fft,
        );
        let mut correction = quotient.coefficients;
        fft.fft(log - 1, coset, &mut correction);
        correction.extend(quotient.evaluations);
        blas::mul(&mut correction, &self.vanishing, field);
        correction
    }
}

/// A contiguous destination segment inside one source-sized additive coset.
struct OutputBlock {
    output: Range<usize>,
    coset: usize,
    local: usize,
}

impl OutputBlock {
    /// Partition only destinations outside the known source. XOR translation
    /// maps each physical block into the source coset's coefficient coordinates.
    fn cover(ranges: &Ranges, size: usize, source_base: usize) -> Vec<Self> {
        let mut blocks = Vec::new();
        for segment in ranges.outside() {
            let mut begin = segment.start;
            while begin < segment.end {
                let base = begin & !(size - 1);
                let end = segment.end.min(base + size);
                blocks.push(Self {
                    output: begin - ranges.destination.start..end - ranges.destination.start,
                    coset: base ^ source_base,
                    local: begin - base,
                });
                begin = end;
            }
        }
        blocks
    }
}

/// A source transform and the cosets needed to cover its requested outputs.
struct RangeTransform<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> {
    fft: Lch14<'a, W, F>,
    transform: BinaryTransform,
    blocks: Vec<OutputBlock>,
}

impl<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> RangeTransform<'a, W, F> {
    /// Use the smallest aligned additive coset enclosing both source endpoints.
    fn new(ranges: &Ranges, field: &'a F, subfield: &'a BinarySubfield) -> Self {
        let source = &ranges.source;
        let log = (usize::BITS - (source.start ^ (source.end - 1)).leading_zeros()) as usize;
        let size = 1 << log;
        let base = source.start & !(size - 1);
        let fft = Lch14::new(field, subfield);
        let transform =
            BinaryTransform::new(size, 0, source.start - base, source.len(), &fft, field);
        let blocks = OutputBlock::cover(ranges, size, base);
        Self {
            fft,
            transform,
            blocks,
        }
    }

    /// Recover the degree-bounded polynomial once, then evaluate each requested
    /// coset. An output in the source coset reuses the mixed transform's values.
    fn apply(&self, source: &[Gf2_128], destination: &mut [Gf2_128], field: &F) {
        let tail = vec![field.zero(); self.transform.size() - source.len()];
        let result = self.transform.apply(source, &tail, &self.fft, field);
        let mut work = vec![field.zero(); self.transform.size()];
        for block in &self.blocks {
            let values = if block.coset == 0 {
                &result.evaluations
            } else {
                work.copy_from_slice(&result.coefficients);
                self.fft.fft(self.transform.log, block.coset, &mut work);
                &work
            };
            destination[block.output.clone()]
                .copy_from_slice(&values[block.local..block.local + block.output.len()]);
        }
    }
}

/// Binary range interpolation using a single sequential vanishing-polynomial merge.
pub struct BinaryInterpolationPlan<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> {
    field: &'a F,
    ranges: Ranges,
    transform: Option<RangeTransform<'a, W, F>>,
}

impl<const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> InterpolationPlan<W, F>
    for BinaryInterpolationPlan<'_, W, F>
{
    fn apply(&self, source: &[F::E]) -> Vec<F::E> {
        let mut destination = vec![self.field.zero(); self.ranges.destination.len()];
        if !self.ranges.trivial(source, &mut destination) {
            self.transform
                .as_ref()
                .unwrap()
                .apply(source, &mut destination, self.field);
        }
        destination
    }
}

impl<'a, const W: usize, F: RuntimeBinaryField<W, E = Gf2_128>> RangeInterpolatorFactory<W, F>
    for BinaryInterpolatorFactory<'a, W, F>
{
    type Plan = BinaryInterpolationPlan<'a, W, F>;

    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool {
        Ranges::valid(&source, &destination, 1 << self.subfield.dimension())
    }

    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "unsupported binary interpolation ranges"
        );
        let ranges = Ranges::new(source, destination);
        let transform = ranges
            .needs_work()
            .then(|| RangeTransform::new(&ranges, self.field, self.subfield));
        BinaryInterpolationPlan {
            field: self.field,
            ranges,
            transform,
        }
    }

    fn point(&self, index: usize) -> F::E {
        assert!(
            index < 1 << self.subfield.dimension(),
            "point outside binary domain"
        );
        self.subfield.embed(index as u64)
    }
}

impl<const W: usize, F> crate::runtime::algebra::EvaluationDomain<W, F>
    for BinaryInterpolatorFactory<'_, W, F>
where F: RuntimeBinaryField<W, E = Gf2_128> + crate::core::algebra::SerializableField
{
    fn domain_id(&self) -> Vec<u8> {
        let mut id = b"gf2_128/lch14-prefix/v1".to_vec();
        for point in self.subfield.basis() {
            id.extend(self.field.to_bytes(point));
        }
        id
    }
}

#[cfg(test)]
#[path = "../../tests/all/binary.rs"]
mod tests;
