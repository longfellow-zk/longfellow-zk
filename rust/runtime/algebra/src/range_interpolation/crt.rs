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

//! Experimental componentwise interpolation with exact CRT convolution.
use std::ops::Range;

use super::{
    arithmetic::{ArithmeticBlock, ArithmeticGeometry},
    crt_fft::{
        crt_from_u64, crt_mul, crt_pow, crt_to_u64, fft_backward, root_for_size, root_table,
        CRT_OMEGA_ORDER, CRT_PRIME,
    },
    InterpolationPlan, RangeInterpolatorFactory, Ranges,
};
use crate::{
    core::algebra::{
        fp24::{add_base, invert_base, mul_base, sub_base, Q},
        AlgebraicField, BareField, SupportsU64Conversions,
    },
    runtime::algebra::fp24_ext6::{RuntimeElement, RuntimeFp24Ext6, EXTENSION_DEGREE},
};

/// Experimental interpolation using exact componentwise CRT convolution.
#[derive(Clone, Copy, Debug, Default)]
pub struct CrtInterpolatorFactory;

struct BaseField;
impl BareField for BaseField {
    type E = u32;
}
impl AlgebraicField for BaseField {
    fn zero(&self) -> u32 {
        0
    }
    fn one(&self) -> u32 {
        1
    }
    fn add(&self, a: &mut u32, b: &u32) {
        *a = add_base(*a, *b);
    }
    fn sub(&self, a: &mut u32, b: &u32) {
        *a = sub_base(*a, *b);
    }
    fn mul(&self, a: &mut u32, b: &u32) {
        *a = mul_base(*a, *b);
    }
    fn invert(&self, a: &u32) -> u32 {
        invert_base(*a)
    }
}
impl SupportsU64Conversions for BaseField {
    fn u64_to_element(&self, n: u64) -> u32 {
        (n % u64::from(Q)) as u32
    }
}

struct Block {
    output: Range<usize>,
    spectrum: Vec<u64>,
    factors: Vec<u32>,
}

impl Block {
    /// Prepare the public reciprocal kernel in the auxiliary prime field.
    /// Inverse-FFT normalization is included once, rather than on every row.
    fn prepare(block: ArithmeticBlock<u32>, inverse_roots: &[u64], scale: u64) -> Self {
        let mut spectrum: Vec<_> = block
            .kernel
            .into_iter()
            .map(|value| crt_mul(crt_from_u64(u64::from(value)), scale))
            .collect();
        fft_backward(&mut spectrum, inverse_roots);
        Self {
            output: block.output,
            spectrum,
            factors: block.factors,
        }
    }

    /// The CRT bound guarantees the convolution is an exact integer sum.
    /// Reduce it to the base field, scale it, and write this extension component.
    fn write_component(
        &self,
        work: &[u64],
        destination: &mut [RuntimeElement],
        component: usize,
        f: &RuntimeFp24Ext6,
    ) {
        let output = &mut destination[self.output.clone()];
        for i in 0..output.len() {
            let mut coefficients = *output[i].coefficients();
            coefficients[component] =
                mul_base((crt_to_u64(work[i]) % u64::from(Q)) as u32, self.factors[i]);
            output[i] = f.from_coefficients(coefficients);
        }
    }
}

/// Experimental range interpolation for the six-component MLDSA field.
pub struct CrtInterpolationPlan {
    ranges: Ranges,
    weights: Vec<u32>,
    roots: Vec<u64>,
    inverse_roots: Vec<u64>,
    blocks: Vec<Block>,
}
impl CrtInterpolationPlan {
    fn new(source: Range<usize>, destination: Range<usize>) -> Self {
        let ranges = Ranges::new(source, destination);
        let geometry = ArithmeticGeometry::new(&ranges, CRT_OMEGA_ORDER, &BaseField);
        let mut roots = Vec::new();
        let mut inverse_roots = Vec::new();
        if geometry.padding != 0 {
            let root = root_for_size(geometry.padding);
            roots = root_table(root, geometry.padding);
            inverse_roots = root_table(crt_pow(root, CRT_PRIME - 2), geometry.padding);
        }
        let scale = if geometry.padding != 0 {
            crt_pow(crt_from_u64(geometry.padding as u64), CRT_PRIME - 2)
        } else {
            0
        };
        let blocks = geometry
            .blocks
            .into_iter()
            .map(|block| Block::prepare(block, &inverse_roots, scale))
            .collect();
        Self {
            ranges,
            weights: geometry.weights,
            roots,
            inverse_roots,
            blocks,
        }
    }
    /// Weight and transform one base-field component, sharing its spectrum
    /// across all destination blocks. Reuse the buffer for the next component.
    fn prepare_component(&self, source: &[RuntimeElement], component: usize, prepared: &mut [u64]) {
        prepared.fill(0);
        for i in 0..source.len() {
            prepared[i] = crt_from_u64(u64::from(mul_base(
                source[i].coefficients()[component],
                self.weights[i],
            )));
        }
        fft_backward(prepared, &self.inverse_roots);
    }
}
impl InterpolationPlan<3, RuntimeFp24Ext6> for CrtInterpolationPlan {
    /// Apply independent exact convolutions to all extension components.
    fn apply(&self, source: &[RuntimeElement]) -> Vec<RuntimeElement> {
        let f = RuntimeFp24Ext6::new();
        let mut destination = vec![f.zero(); self.ranges.destination.len()];
        if self.ranges.trivial(source, &mut destination) {
            return destination;
        }
        let mut prepared = vec![0; self.roots.len()];
        let mut work = vec![0; self.roots.len()];
        for component in 0..EXTENSION_DEGREE {
            self.prepare_component(source, component, &mut prepared);
            for block in &self.blocks {
                for i in 0..work.len() {
                    work[i] = crt_mul(prepared[i], block.spectrum[i]);
                }
                fft_backward(&mut work, &self.roots);
                block.write_component(&work, &mut destination, component, &f);
            }
        }
        destination
    }
}
impl RangeInterpolatorFactory<3, RuntimeFp24Ext6> for CrtInterpolatorFactory {
    type Plan = CrtInterpolationPlan;
    fn can_interpolate(&self, source: Range<usize>, destination: Range<usize>) -> bool {
        if !Ranges::valid(&source, &destination, Q as usize) {
            return false;
        }
        let ranges = Ranges::new(source, destination);
        !ranges.needs_work()
            || (ranges.source.len() <= CRT_OMEGA_ORDER
                && (ranges.source.len() as u128) * u128::from(Q - 1).pow(2) < u128::from(CRT_PRIME))
    }
    fn make_range(&self, source: Range<usize>, destination: Range<usize>) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "unsupported CRT interpolation ranges"
        );
        CrtInterpolationPlan::new(source, destination)
    }
    fn point(&self, index: usize) -> RuntimeElement {
        assert!(index < Q as usize, "point outside CRT domain");
        RuntimeFp24Ext6::new().u64_to_element(index as u64)
    }
}

impl crate::runtime::algebra::EvaluationDomain<3, RuntimeFp24Ext6> for CrtInterpolatorFactory {
    fn domain_id(&self) -> Vec<u8> {
        b"fp24/ext6/beta7/arithmetic-prefix/v1".to_vec()
    }
}
