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

//! Public weights for shifted reciprocal convolution, shared by FFT and CRT.
//! Barycentric interpolation at consecutive arithmetic points is a convolution
//! against reciprocal differences, followed by a falling-factorial scale.
use std::ops::Range;

use super::{batch_inverse, difference, Ranges};
use crate::core::algebra::{AlgebraicField, SupportsU64Conversions};

/// One output block's reciprocal kernel and final barycentric scale factors.
pub(super) struct ArithmeticBlock<E> {
    pub(super) output: Range<usize>,
    pub(super) kernel: Vec<E>,
    pub(super) factors: Vec<E>,
}

/// Backend-independent preprocessing; FFT backends transform the kernels once.
pub(super) struct ArithmeticGeometry<E> {
    pub(super) weights: Vec<E>,
    pub(super) blocks: Vec<ArithmeticBlock<E>>,
    pub(super) padding: usize,
}

impl<E: Clone> ArithmeticGeometry<E> {
    /// Choose a common transform size so all output blocks reuse the input FFT.
    pub(super) fn new<F: AlgebraicField<E = E> + SupportsU64Conversions>(
        ranges: &Ranges,
        max_transform: usize,
        field: &F,
    ) -> Self {
        if !ranges.needs_work() {
            return Self {
                weights: Vec::new(),
                blocks: Vec::new(),
                padding: 0,
            };
        }
        let count = ranges.source.len();
        let outside = ranges.outside();
        let block_len = count
            .min(max_transform - count + 1)
            .min(outside.iter().map(Range::len).max().unwrap());
        let padding = (count + block_len - 1).next_power_of_two();
        assert!(padding <= max_transform);
        let blocks = outside
            .into_iter()
            .flat_map(|segment| segment_blocks(ranges, segment, block_len, padding, field))
            .collect();
        Self {
            weights: source_weights(count, field),
            blocks,
            padding,
        }
    }
}

/// For source index i, compute 1 / (i! * (-1)^(k-1-i) * (k-1-i)!).
fn source_weights<F: AlgebraicField + SupportsU64Conversions>(
    count: usize,
    field: &F,
) -> Vec<F::E> {
    let mut factorial = vec![field.one(); count];
    for i in 1..count {
        factorial[i] = field.mulf(&factorial[i - 1], &field.u64_to_element(i as u64));
    }
    let denominators: Vec<_> = (0..count)
        .map(|i| field.mulf(&factorial[i], &factorial[count - 1 - i]))
        .collect();
    let mut weights = batch_inverse(&denominators, field);
    for (i, weight) in weights.iter_mut().enumerate() {
        if (count - 1 - i) & 1 != 0 {
            *weight = field.neg(weight);
        }
    }
    weights
}

/// Partition one side of the overlap, carrying its falling factorial between
/// adjacent blocks. A fresh nonzero product starts each disjoint segment.
fn segment_blocks<F: AlgebraicField + SupportsU64Conversions>(
    ranges: &Ranges,
    segment: Range<usize>,
    block_len: usize,
    padding: usize,
    field: &F,
) -> Vec<ArithmeticBlock<F::E>> {
    let mut factor = field.one();
    for i in ranges.source.clone() {
        field.mul(&mut factor, &difference(segment.start, i, field));
    }
    let mut blocks = Vec::new();
    let mut begin = segment.start;
    while begin < segment.end {
        let count = block_len.min(segment.end - begin);
        let kernel = reciprocal_kernel(&ranges.source, begin, count, padding, field);
        let factors = destination_factors(
            &ranges.source,
            begin..begin + count,
            segment.end,
            &mut factor,
            field,
        );
        blocks.push(ArithmeticBlock {
            output: begin - ranges.destination.start..begin - ranges.destination.start + count,
            kernel,
            factors,
        });
        begin += count;
    }
    blocks
}

/// Place reciprocal differences at cyclic lags -(k-1)..count-1. With this
/// padding, cyclic convolution coefficients 0..count equal the desired sums.
fn reciprocal_kernel<F: AlgebraicField + SupportsU64Conversions>(
    source: &Range<usize>,
    begin: usize,
    count: usize,
    padding: usize,
    field: &F,
) -> Vec<F::E> {
    let k = source.len();
    let lags: Vec<_> = (0..k + count - 1)
        .map(|r| {
            field.addf(
                &difference(begin, source.start, field),
                &difference(r, k - 1, field),
            )
        })
        .collect();
    let mut kernel = vec![field.zero(); padding];
    for (r, value) in batch_inverse(&lags, field).into_iter().enumerate() {
        kernel[(r + padding - (k - 1)) % padding] = value;
    }
    kernel
}

/// Emit Z_source(j), updating the product with
/// Z_source(j+1) = Z_source(j) * (j+1-source.start) / (j+1-source.end).
fn destination_factors<F: AlgebraicField + SupportsU64Conversions>(
    source: &Range<usize>,
    destination: Range<usize>,
    segment_end: usize,
    factor: &mut F::E,
    field: &F,
) -> Vec<F::E> {
    let denominators: Vec<_> = destination
        .clone()
        .map(|j| difference(j + 1, source.end, field))
        .collect();
    let mut factors = Vec::with_capacity(destination.len());
    for (j, inverse) in destination.zip(batch_inverse(&denominators, field)) {
        factors.push(factor.clone());
        if j + 1 < segment_end {
            field.mul(factor, &difference(j + 1, source.start, field));
            field.mul(factor, &inverse);
        }
    }
    factors
}

/// Arithmetic backends have the same identity regardless of their FFT machinery.
pub(super) fn evaluation_domain_id<F: crate::core::algebra::SerializableField>(
    field: &F,
) -> Vec<u8> {
    let mut id = b"prime/arithmetic-prefix/v1".to_vec();
    id.extend(field.serialized_mone());
    id
}
