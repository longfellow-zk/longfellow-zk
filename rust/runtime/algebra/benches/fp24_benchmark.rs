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

use longfellow_zk::{
    core::algebra::{AlgebraicField, SupportsU64Conversions},
    runtime::algebra::{
        fp24_ext6::{RuntimeFp24Ext6, Q},
        InterpolationPlan, RangeInterpolatorFactory,
    },
};

fn bit_reverse_permute<T>(values: &mut [T]) {
    let mut reversed = 0;
    for i in 0..values.len() - 1 {
        if i < reversed {
            values.swap(i, reversed);
        }
        let mut bit = values.len();
        loop {
            bit >>= 1;
            reversed ^= bit;
            if reversed & bit != 0 {
                break;
            }
        }
    }
}

fn pow_base(mut base: u32, mut exponent: u32) -> u32 {
    let mut result = 1u32;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = (u64::from(result) * u64::from(base) % u64::from(Q)) as u32;
        }
        base = (u64::from(base) * u64::from(base) % u64::from(Q)) as u32;
        exponent >>= 1;
    }
    result
}

fn fft_fp24(values: &mut [u32]) {
    let n = values.len();
    bit_reverse_permute(values);
    let root = pow_base(283_817, (8192 / n) as u32);
    let mut roots = vec![1u32; n];
    for i in 1..n {
        roots[i] = (u64::from(roots[i - 1]) * u64::from(root) % u64::from(Q)) as u32;
    }
    let mut width = 2;
    while width <= values.len() {
        for block in values.chunks_exact_mut(width) {
            let (low, high) = block.split_at_mut(width / 2);
            let old_a = low[0];
            low[0] = if old_a + high[0] >= Q {
                old_a + high[0] - Q
            } else {
                old_a + high[0]
            };
            high[0] = if old_a >= high[0] {
                old_a - high[0]
            } else {
                old_a + Q - high[0]
            };
            for (j, (a, b)) in low.iter_mut().zip(high).enumerate().skip(1) {
                let twiddle = roots[j * n / width];
                let product = (u64::from(*b) * u64::from(twiddle) % u64::from(Q)) as u32;
                let previous = *a;
                *a = if previous + product >= Q {
                    previous + product - Q
                } else {
                    previous + product
                };
                *b = if previous >= product {
                    previous - product
                } else {
                    previous + Q - product
                };
            }
        }
        width *= 2;
    }
}

fn fft_fp24_6(
    field: &RuntimeFp24Ext6,
    values: &mut [longfellow_zk::runtime::algebra::fp24_ext6::RuntimeElement],
) {
    assert_eq!(values.len(), 8192);
    let n = values.len();
    bit_reverse_permute(values);
    let root = field.u64_to_element(283_817);
    let mut roots = vec![field.one(); n];
    for i in 1..n {
        let previous = roots[i - 1];
        roots[i] = field.mulf(&previous, &root);
    }
    let mut width = 2;
    while width <= values.len() {
        for block in values.chunks_exact_mut(width) {
            let (low, high) = block.split_at_mut(width / 2);
            let old_a = low[0];
            let old_b = high[0];
            field.add(&mut low[0], &old_b);
            high[0] = old_a;
            field.sub(&mut high[0], &old_b);
            for (j, (a, b)) in low.iter_mut().zip(high).enumerate().skip(1) {
                let twiddle = roots[j * n / width];
                let mut product = *b;
                field.mul(&mut product, &twiddle);
                let previous = *a;
                field.add(a, &product);
                *b = previous;
                field.sub(b, &product);
            }
        }
        width *= 2;
    }
}

fn main() {
    const N: usize = 8192;
    let mut base: Vec<_> = (0..N)
        .map(|i| ((i as u64 * 1_103_515_245 + 12_345) % u64::from(Q)) as u32)
        .collect();
    let base_start = std::time::Instant::now();
    for _ in 0..100 {
        fft_fp24(std::hint::black_box(&mut base));
    }
    let fp24 = base_start.elapsed() / 100;

    let field = RuntimeFp24Ext6::new();
    let mut extension: Vec<_> = (0..N)
        .map(|i| {
            field.from_coefficients(std::array::from_fn(|j| {
                ((i as u64 * 1_103_515_245 + j as u64 * 97 + 12_345) % u64::from(Q)) as u32
            }))
        })
        .collect();
    let extension_start = std::time::Instant::now();
    for _ in 0..20 {
        fft_fp24_6(&field, std::hint::black_box(&mut extension));
    }
    let fp24_6 = extension_start.elapsed() / 20;

    let factory = longfellow_zk::runtime::algebra::range_interpolation::CrtInterpolatorFactory;
    let rs = factory.make_range(0..950, 950..5699);
    let source: Vec<_> = (0..950)
        .map(|i| {
            field.from_coefficients(std::array::from_fn(|j| {
                ((i * 131 + j * 17 + 1) % Q as usize) as u32
            }))
        })
        .collect();
    let crt_start = std::time::Instant::now();
    for _ in 0..20 {
        std::hint::black_box(rs.apply(std::hint::black_box(&source)));
    }
    let crt = crt_start.elapsed() / 20;

    eprintln!(
        "Prime-field extension algebra benchmark: FFT Fp24/8192={fp24:?}; FFT Fp24_6/8192={fp24_6:?}; CRT RS(950,5699)={crt:?}"
    );
    std::hint::black_box((base, extension, source));
}
