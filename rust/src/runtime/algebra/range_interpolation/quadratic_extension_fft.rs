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
    arithmetic::{ArithmeticBlock, ArithmeticGeometry},
    InterpolationPlan, RangeInterpolatorFactory, Ranges,
};
use crate::{
    core::algebra::{Nat, SupportsNatConversions, SupportsU64Conversions},
    runtime::algebra::{
        blas,
        field::SupportsQuadraticExtension,
        fp2::{Fp2Element, Fp2Field},
        rfft,
    },
};

/// Arithmetic point-table interpolation using real FFT convolution.
/// Requires a quadratic extension field and a power-of-two root of unity in
/// that extension. The interpolation points and values remain in the base field.
pub struct QuadraticExtensionFftInterpolatorFactory<
    'a,
    const W: usize,
    F: SupportsQuadraticExtension<W> + SupportsU64Conversions,
> {
    f: &'a F,
    f2: &'a Fp2Field<'a, W, F>,
    omega: Fp2Element<W, F>,
    omega_order: u64,
}

impl<'a, const W: usize, F: SupportsQuadraticExtension<W> + SupportsU64Conversions>
    QuadraticExtensionFftInterpolatorFactory<'a, W, F>
{
    pub fn new(
        f: &'a F,
        f2: &'a Fp2Field<'a, W, F>,
        omega: Fp2Element<W, F>,
        omega_order: u64,
    ) -> Self {
        Self {
            f,
            f2,
            omega,
            omega_order,
        }
    }
}

// The radix-two FFT kernels require a power-of-two root order.
fn max_transform(order: u64) -> usize {
    if !order.is_power_of_two() {
        return 0;
    }
    1usize << order.trailing_zeros().min(usize::BITS - 1)
}

struct Block<E> {
    output: Range<usize>,
    kernel_fft: Vec<E>,
    factors: Vec<E>,
}

impl<E> Block<E> {
    /// Transform and normalize a public reciprocal kernel once per output block.
    fn prepare<const W: usize, F: SupportsQuadraticExtension<W, E = E> + SupportsU64Conversions>(
        block: ArithmeticBlock<E>,
        scale: &E,
        factory: &QuadraticExtensionFftInterpolatorFactory<'_, W, F>,
    ) -> Self {
        let mut kernel_fft = block.kernel;
        rfft::r2hc(
            &mut kernel_fft,
            &factory.omega,
            factory.omega_order,
            factory.f2,
        );
        blas::scale(&mut kernel_fft, scale, factory.f);
        Self {
            output: block.output,
            kernel_fft,
            factors: block.factors,
        }
    }
}

/// Shifted arithmetic interpolation using blocked real FFT convolutions.
pub struct QuadraticExtensionFftInterpolationPlan<
    'a,
    const W: usize,
    F: SupportsQuadraticExtension<W> + SupportsU64Conversions,
> {
    f: &'a F,
    f2: &'a Fp2Field<'a, W, F>,
    omega: Fp2Element<W, F>,
    omega_order: u64,
    ranges: Ranges,
    weights: Vec<F::E>,
    padding: usize,
    blocks: Vec<Block<F::E>>,
}

impl<'a, const W: usize, F: SupportsQuadraticExtension<W> + SupportsU64Conversions>
    QuadraticExtensionFftInterpolationPlan<'a, W, F>
{
    fn new(
        factory: &QuadraticExtensionFftInterpolatorFactory<'a, W, F>,
        source: Range<usize>,
        destination: Range<usize>,
    ) -> Self {
        let ranges = Ranges::new(source, destination);
        let geometry =
            ArithmeticGeometry::new(&ranges, max_transform(factory.omega_order), factory.f);
        let scale = if geometry.padding != 0 {
            factory
                .f
                .invert(&factory.f.u64_to_element(geometry.padding as u64))
        } else {
            factory.f.one()
        };
        let blocks = geometry
            .blocks
            .into_iter()
            .map(|block| Block::prepare(block, &scale, factory))
            .collect();
        Self {
            f: factory.f,
            f2: factory.f2,
            omega: factory.omega.clone(),
            omega_order: factory.omega_order,
            ranges,
            weights: geometry.weights,
            padding: geometry.padding,
            blocks,
        }
    }
}

/// Multiply two real-FFT spectra, retaining the prepared input unchanged.
fn multiply_spectra<const W: usize, F: SupportsQuadraticExtension<W>>(
    out: &mut [F::E],
    kernel: &[F::E],
    f: &F,
) {
    f.mul(&mut out[0], &kernel[0]);
    let half = out.len() / 2;
    f.mul(&mut out[half], &kernel[half]);
    let (left, right) = out.split_at_mut(half);
    for j in 1..half {
        rfft::cmul::<W, F>(
            &mut left[j],
            &mut right[half - j],
            &kernel[j],
            &kernel[2 * half - j],
            f,
        );
    }
}

impl<const W: usize, F: SupportsQuadraticExtension<W> + SupportsU64Conversions>
    InterpolationPlan<W, F> for QuadraticExtensionFftInterpolationPlan<'_, W, F>
{
    fn apply(&self, source: &[F::E]) -> Vec<F::E> {
        let mut destination = vec![self.f.zero(); self.ranges.destination.len()];
        if self.ranges.trivial(source, &mut destination) {
            return destination;
        }
        let mut prepared = vec![self.f.zero(); self.padding];
        prepared[..source.len()].clone_from_slice(source);
        blas::mul(&mut prepared[..source.len()], &self.weights, self.f);
        rfft::r2hc(&mut prepared, &self.omega, self.omega_order, self.f2);
        let mut work = vec![self.f.zero(); self.padding];
        for block in &self.blocks {
            work.clone_from_slice(&prepared);
            multiply_spectra::<W, F>(&mut work, &block.kernel_fft, self.f);
            rfft::hc2r(&mut work, &self.omega, self.omega_order, self.f2);
            let output = &mut destination[block.output.clone()];
            output.clone_from_slice(&work[..output.len()]);
            blas::mul(output, &block.factors, self.f);
        }
        destination
    }
}

impl<'a, const W: usize, F> RangeInterpolatorFactory<W, F>
    for QuadraticExtensionFftInterpolatorFactory<'a, W, F>
where F: SupportsQuadraticExtension<W> + SupportsU64Conversions + SupportsNatConversions<W>
{
    type Plan = QuadraticExtensionFftInterpolationPlan<'a, W, F>;
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool {
        if !Ranges::valid(&source, &destination, usize::MAX) {
            return false;
        }
        let last = source.end.max(destination.end) - 1;
        if u64::try_from(last).is_err()
            || F::N::from_u64(last as u64) > self.f.to_nat(&self.f.mone())
        {
            return false;
        }
        let ranges = Ranges::new(source, destination);
        !ranges.needs_work() || ranges.source.len() <= max_transform(self.omega_order)
    }
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "unsupported quadratic-extension FFT interpolation ranges"
        );
        QuadraticExtensionFftInterpolationPlan::new(self, source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        let index_u64 = u64::try_from(index).expect("point index exceeds u64");
        assert!(
            F::N::from_u64(index_u64) <= self.f.to_nat(&self.f.mone()),
            "point outside arithmetic domain"
        );
        self.f.u64_to_element(index_u64)
    }
}

impl<const W: usize, F> crate::runtime::algebra::EvaluationDomain<W, F>
    for QuadraticExtensionFftInterpolatorFactory<'_, W, F>
where F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + SupportsU64Conversions
        + SupportsNatConversions<W>
        + SupportsQuadraticExtension<W>
{
    fn field(&self) -> &F {
        self.f
    }
    fn domain_id(&self) -> Vec<u8> {
        super::arithmetic::evaluation_domain_id(self.f)
    }
}
