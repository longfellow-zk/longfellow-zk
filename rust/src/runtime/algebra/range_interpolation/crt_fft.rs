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

//! Internal Montgomery arithmetic and FFT for exact CRT convolutions.

pub(super) const CRT_PRIME: u64 = 18_446_744_072_195_407_873;
const CRT_OMEGA: u64 = 436_037_131_817;
pub(super) const CRT_OMEGA_ORDER: usize = 1 << 22;
const CRT_MONTGOMERY_ONE: u64 = 1_514_143_743;
const CRT_MONTGOMERY_R2: u64 = 2_292_631_274_466_050_049;
const CRT_MONTGOMERY_NPRIME: u64 = 16_154_112_794_701_070_335;

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
pub(super) fn crt_mul(a: u64, b: u64) -> u64 {
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
pub(super) fn crt_from_u64(value: u64) -> u64 {
    crt_mul(value, CRT_MONTGOMERY_R2)
}

#[inline]
pub(super) fn crt_to_u64(value: u64) -> u64 {
    crt_mul(value, 1)
}

pub(super) fn crt_pow(mut base: u64, mut exponent: u64) -> u64 {
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
pub(super) fn fft_backward(values: &mut [u64], roots: &[u64]) {
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

pub(super) fn root_table(root: u64, size: usize) -> Vec<u64> {
    let mut roots = vec![CRT_MONTGOMERY_ONE; size];
    for i in 1..size {
        roots[i] = crt_mul(roots[i - 1], root);
    }
    roots
}

pub(super) fn root_for_size(size: usize) -> u64 {
    assert!(size.is_power_of_two());
    assert!(size <= CRT_OMEGA_ORDER);
    crt_pow(crt_from_u64(CRT_OMEGA), (CRT_OMEGA_ORDER / size) as u64)
}
