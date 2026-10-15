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

//! CRT-backed Reed-Solomon interpolation for the ML-DSA sextic field.
//!
//! This mirrors the C++ `ReedSolomonExtension6`: interpolation points and each
//! coefficient live in F_q, while convolution is accelerated with a 2^22 root
//! of unity in a 64-bit CRT prime. Each of the six extension coefficients is
//! encoded independently and then recombined.

use runtime_algebra::{Interpolator, InterpolatorFactory};

use super::algebra::{RuntimeElement, RuntimeFp24Ext6, EXTENSION_DEGREE, Q};

const CRT_PRIME: u64 = 18_446_744_072_195_407_873;
const CRT_OMEGA: u64 = 436_037_131_817;
const CRT_OMEGA_ORDER: usize = 1 << 22;
const CRT_MONTGOMERY_ONE: u64 = 1_514_143_743;
const CRT_MONTGOMERY_R2: u64 = 2_292_631_274_466_050_049;
const CRT_MONTGOMERY_NPRIME: u64 = 16_154_112_794_701_070_335;

#[inline]
fn q_add(a: u32, b: u32) -> u32 {
    let sum = a + b;
    if sum >= Q {
        sum - Q
    } else {
        sum
    }
}

#[inline]
fn q_sub(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        a + Q - b
    }
}

#[inline]
fn q_mul(a: u32, b: u32) -> u32 {
    (u64::from(a) * u64::from(b) % u64::from(Q)) as u32
}

fn q_pow(mut base: u32, mut exponent: u32) -> u32 {
    let mut result = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = q_mul(result, base);
        }
        base = q_mul(base, base);
        exponent >>= 1;
    }
    result
}

#[inline]
fn crt_add(a: u64, b: u64) -> u64 {
    let (sum, overflow) = a.overflowing_add(b);
    if overflow {
        sum + (u64::MAX - CRT_PRIME + 1)
    } else if sum >= CRT_PRIME {
        sum - CRT_PRIME
    } else {
        sum
    }
}

#[inline]
fn crt_sub(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        CRT_PRIME - (b - a)
    }
}

#[inline]
fn crt_mul(a: u64, b: u64) -> u64 {
    // One-limb Montgomery reduction. Unlike `% CRT_PRIME`, this compiles to
    // multiplies/adds rather than a 128-by-64 division in every FFT butterfly.
    let product = u128::from(a) * u128::from(b);
    let low = product as u64;
    let high = (product >> 64) as u64;
    let multiplier = low.wrapping_mul(CRT_MONTGOMERY_NPRIME);
    let correction = u128::from(multiplier) * u128::from(CRT_PRIME);
    let (_, carry) = low.overflowing_add(correction as u64);
    let (partial, overflow0) = high.overflowing_add((correction >> 64) as u64);
    let (value, overflow1) = partial.overflowing_add(u64::from(carry));
    if overflow0 || overflow1 {
        value.wrapping_add(u64::MAX - CRT_PRIME + 1)
    } else if value >= CRT_PRIME {
        value - CRT_PRIME
    } else {
        value
    }
}

#[inline]
fn crt_from_u64(value: u64) -> u64 {
    crt_mul(value, CRT_MONTGOMERY_R2)
}

#[inline]
fn crt_to_u64(value: u64) -> u64 {
    crt_mul(value, 1)
}

fn crt_pow(mut base: u64, mut exponent: u64) -> u64 {
    let mut result = CRT_MONTGOMERY_ONE;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = crt_mul(result, base);
        }
        base = crt_mul(base, base);
        exponent >>= 1;
    }
    result
}

fn bit_reverse_permute(values: &mut [u64]) {
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

/// Unscaled inverse-direction FFT, matching the C++ `FFTB` convention.
fn fft_backward(values: &mut [u64], roots: &[u64]) {
    assert_eq!(values.len(), roots.len());
    let n = values.len();
    bit_reverse_permute(values);
    let mut width = 2;
    while width <= n {
        for block in values.chunks_exact_mut(width) {
            let (low, high) = block.split_at_mut(width / 2);
            let old_a = low[0];
            low[0] = crt_add(old_a, high[0]);
            high[0] = crt_sub(old_a, high[0]);
            for j in 1..width / 2 {
                let product = crt_mul(high[j], roots[j * n / width]);
                let a = &mut low[j];
                let previous_a = *a;
                *a = crt_add(previous_a, product);
                high[j] = crt_sub(previous_a, product);
            }
        }
        width *= 2;
    }
}

fn root_table(root: u64, size: usize) -> Vec<u64> {
    let mut roots = vec![CRT_MONTGOMERY_ONE; size];
    for i in 1..size {
        roots[i] = crt_mul(roots[i - 1], root);
    }
    roots
}

fn root_for_size(size: usize) -> u64 {
    assert!(size.is_power_of_two());
    assert!(size <= CRT_OMEGA_ORDER);
    crt_pow(crt_from_u64(CRT_OMEGA), (CRT_OMEGA_ORDER / size) as u64)
}

struct CrtMiddleProduct {
    n: usize,
    padding: usize,
    roots: Vec<u64>,
    inverse_roots: Vec<u64>,
    kernel_fft: Vec<u64>,
}

impl CrtMiddleProduct {
    fn new(n: usize, m: usize, kernel: &[u32]) -> Self {
        assert!(n > 0 && m >= n && kernel.len() == m);
        let padding = m.next_power_of_two();
        assert!(padding <= CRT_OMEGA_ORDER);
        let root = root_for_size(padding);
        let roots = root_table(root, padding);
        let inverse_roots = root_table(crt_pow(root, CRT_PRIME - 2), padding);
        let inverse_padding = crt_pow(crt_from_u64(padding as u64), CRT_PRIME - 2);
        let mut kernel_fft = vec![0; padding];
        for (dst, &src) in kernel_fft.iter_mut().zip(kernel) {
            *dst = crt_mul(crt_from_u64(u64::from(src)), inverse_padding);
        }
        fft_backward(&mut kernel_fft, &inverse_roots);
        Self {
            n,
            padding,
            roots,
            inverse_roots,
            kernel_fft,
        }
    }

    fn middle_product(&self, x: &[u32], values: &mut [u64]) {
        assert_eq!(x.len(), self.n);
        assert_eq!(values.len(), self.padding);
        values.fill(0);
        for (dst, &src) in values.iter_mut().zip(x) {
            *dst = crt_from_u64(u64::from(src));
        }
        fft_backward(values, &self.inverse_roots);
        for (value, &kernel) in values.iter_mut().zip(&self.kernel_fft) {
            *value = crt_mul(*value, kernel);
        }
        fft_backward(values, &self.roots);
    }
}

pub struct CrtReedSolomon {
    field: RuntimeFp24Ext6,
    n: usize,
    m: usize,
    leading_constant: Vec<u32>,
    signed_binomial: Vec<u32>,
    middle_product: CrtMiddleProduct,
}

impl CrtReedSolomon {
    fn new(n: usize, m: usize) -> Self {
        assert!(n > 0 && m >= n && m <= Q as usize);
        let mut inverses = vec![0u32; m];
        let mut product = 1;
        for (i, slot) in inverses.iter_mut().enumerate().skip(1) {
            *slot = product;
            product = q_mul(product, i as u32);
        }
        product = q_pow(product, Q - 2);
        for i in (1..m).rev() {
            inverses[i] = q_mul(inverses[i], product);
            product = q_mul(product, i as u32);
        }

        let degree = n - 1;
        let mut leading_constant = vec![0; m - n + 1];
        leading_constant[0] = 1;
        let mut degree_value = n as u32;
        for i in 1..=m - n {
            leading_constant[i] = q_mul(leading_constant[i - 1], q_mul(degree_value, inverses[i]));
            degree_value = q_add(degree_value, 1);
        }
        for k in degree..m {
            let index = k - degree;
            leading_constant[index] = q_mul(leading_constant[index], index as u32);
            if degree % 2 == 1 && leading_constant[index] != 0 {
                leading_constant[index] = Q - leading_constant[index];
            }
        }

        let mut signed_binomial = vec![0; n];
        signed_binomial[0] = 1;
        let mut binomial_value = degree as u32;
        for i in 1..n {
            signed_binomial[i] = q_mul(signed_binomial[i - 1], q_mul(binomial_value, inverses[i]));
            binomial_value = q_sub(binomial_value, 1);
        }
        for i in (1..n).step_by(2) {
            if signed_binomial[i] != 0 {
                signed_binomial[i] = Q - signed_binomial[i];
            }
        }

        let middle_product = CrtMiddleProduct::new(n, m, &inverses);
        Self {
            field: RuntimeFp24Ext6::new(),
            n,
            m,
            leading_constant,
            signed_binomial,
            middle_product,
        }
    }

    fn interpolate_base(&self, values: &mut [u32], fft_scratch: &mut [u64]) {
        for (i, value) in values.iter_mut().enumerate().take(self.n) {
            *value = q_mul(*value, self.signed_binomial[i]);
        }
        self.middle_product
            .middle_product(&values[..self.n], fft_scratch);
        for i in self.n..self.m {
            let product = (crt_to_u64(fft_scratch[i]) % u64::from(Q)) as u32;
            values[i] = q_mul(self.leading_constant[i - (self.n - 1)], product);
        }
    }
}

impl Interpolator<3, RuntimeFp24Ext6> for CrtReedSolomon {
    fn interpolate(&self, y: &mut [RuntimeElement]) {
        assert_eq!(y.len(), self.m);
        let mut coefficients: Vec<[u32; EXTENSION_DEGREE]> =
            y.iter().map(|element| *element.coefficients()).collect();
        let mut values = vec![0; self.m];
        let mut fft_scratch = vec![0; self.middle_product.padding];
        for degree in 0..EXTENSION_DEGREE {
            for (value, coefficient) in values.iter_mut().zip(&coefficients) {
                *value = coefficient[degree];
            }
            self.interpolate_base(&mut values, &mut fft_scratch);
            for i in self.n..self.m {
                coefficients[i][degree] = values[i];
            }
        }
        for i in self.n..self.m {
            y[i] = self.field.from_coefficients(coefficients[i]);
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CrtReedSolomonFactory;

impl InterpolatorFactory<3, RuntimeFp24Ext6> for CrtReedSolomonFactory {
    type Interpolator = CrtReedSolomon;

    fn make(&self, ylen: usize, block_enc: usize) -> Self::Interpolator {
        CrtReedSolomon::new(ylen, block_enc)
    }

    fn can_encode(&self, ylen: usize, block_enc: usize) -> bool {
        ylen > 0
            && block_enc >= ylen
            && block_enc <= Q as usize
            && block_enc
                .checked_next_power_of_two()
                .is_some_and(|padding| padding <= CRT_OMEGA_ORDER)
    }
}
