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

use super::{gf2_128_accum_reduce, gf2_128_mac, gf2_128_mul, Gf2_128, Gf2_128Accum};

// Independent bit-serial oracle for X^128 + X^7 + X^2 + X + 1.
pub(super) fn reference_mul(mut x: u128, mut y: u128) -> u128 {
    let mut result = 0;
    for _ in 0..128 {
        if y & 1 != 0 {
            result ^= x;
        }
        let carry = x >> 127;
        x <<= 1;
        if carry != 0 {
            x ^= 0x87;
        }
        y >>= 1;
    }
    result
}

pub(super) fn next(state: &mut u128) -> u128 {
    *state ^= *state << 13;
    *state ^= *state >> 17;
    *state ^= *state << 43;
    *state
}

#[test]
fn gf2_128_basis_products() {
    for i in 0..128 {
        for j in 0..128 {
            let raw_x = 1u128 << i;
            let raw_y = 1u128 << j;
            let expected = reference_mul(raw_x, raw_y);
            let x = Gf2_128::from_u128(raw_x);
            let y = Gf2_128::from_u128(raw_y);
            assert_eq!(gf2_128_mul(x, y).to_u128(), expected, "bits {i}, {j}");
            // Exercise the separate load/store and delayed-reduction paths
            // for every pair of input bits, not just multiplication.
            let mut acc = Gf2_128Accum::default();
            gf2_128_mac(&mut acc, &x, &y);
            assert_eq!(
                gf2_128_accum_reduce(&acc).to_u128(),
                expected,
                "accumulated bits {i}, {j}"
            );
            gf2_128_mac(&mut acc, &x, &y);
            assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), 0);
        }
    }
}

#[test]
fn gf2_128_boundary_patterns() {
    let mut values = vec![0, 1, u128::MAX];
    for bit in [1, 7, 8, 15, 16, 31, 32, 63, 64, 65, 95, 96, 120, 126, 127] {
        let x = 1u128 << bit;
        values.extend([x, !x, x - 1, !(x - 1)]);
    }
    // Distinguish all byte lanes, halves, and the XORed Karatsuba inputs.
    values.extend([
        0x5555555555555555_5555555555555555,
        0xaaaaaaaaaaaaaaaa_aaaaaaaaaaaaaaaa,
        0x0102030405060708_090a0b0c0d0e0f10,
        0x8040201008040201_0102040810204080,
        0xfedcba9876543210_fedcba9876543210,
        0xfedcba9876543210_0123456789abcdef,
    ]);
    for &raw_x in &values {
        for &raw_y in &values {
            let expected = reference_mul(raw_x, raw_y);
            let x = Gf2_128::from_u128(std::hint::black_box(raw_x));
            let y = Gf2_128::from_u128(std::hint::black_box(raw_y));
            assert_eq!(gf2_128_mul(x, y).to_u128(), expected);
            assert_eq!(gf2_128_mul(y, x).to_u128(), expected);
            let mut acc = Gf2_128Accum::default();
            // x and y may legally alias one another.
            gf2_128_mac(&mut acc, &x, &x);
            let square = reference_mul(x.to_u128(), x.to_u128());
            assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), square);
            gf2_128_mac(&mut acc, &x, &y);
            let snapshot = acc;
            assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), square ^ expected);
            // Reduction is non-destructive and accumulation can resume.
            assert_eq!(gf2_128_accum_reduce(&acc), gf2_128_accum_reduce(&snapshot));
            gf2_128_mac(&mut acc, &y, &x);
            assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), square);
        }
    }
    assert_eq!(
        gf2_128_mul(Gf2_128::from_u128(1 << 127), Gf2_128::from_u128(2)).to_u128(),
        0x87
    );
}

#[test]
fn gf2_128_all_byte_values_at_top_lane() {
    // Exhaust byte carries and reduction from the highest input byte.
    for byte_x in 0..=255u128 {
        for byte_y in 0..=255u128 {
            let x = byte_x << 120;
            let y = byte_y << 120;
            assert_eq!(
                gf2_128_mul(Gf2_128::from_u128(x), Gf2_128::from_u128(y)).to_u128(),
                reference_mul(x, y),
                "top bytes {x:032x}, {y:032x}"
            );
        }
    }
}

#[test]
fn gf2_128_field_identities() {
    let mut state = 0x876543210fedcba9_1122334455667788;
    for _ in 0..512 {
        let [x, y, z] = core::array::from_fn(|_| Gf2_128::from_u128(next(&mut state)));
        assert_eq!(
            gf2_128_mul(x, y.xor(&z)),
            gf2_128_mul(x, y).xor(&gf2_128_mul(x, z))
        );
        assert_eq!(
            gf2_128_mul(gf2_128_mul(x, y), z),
            gf2_128_mul(x, gf2_128_mul(y, z))
        );
        assert_eq!(gf2_128_mul(x, Gf2_128::from_u128(1)), x);
        assert!(gf2_128_mul(x, Gf2_128::default()).is_zero());
    }
}

#[test]
fn gf2_128_dense_products_and_accumulation() {
    let mut state = 0x123456789abcdef0_fedcba9876543210u128;
    let mut acc = Gf2_128Accum::default();
    let mut expected = 0;
    assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), 0);
    for (raw_x, raw_y) in [(0, u128::MAX), (1, u128::MAX), (u128::MAX, u128::MAX)]
        .into_iter()
        .chain((0..1024).map(|_| (next(&mut state), next(&mut state))))
    {
        let product = reference_mul(raw_x, raw_y);
        let x = Gf2_128::from_u128(raw_x);
        let y = Gf2_128::from_u128(raw_y);
        assert_eq!(gf2_128_mul(x, y).to_u128(), product);
        gf2_128_mac(&mut acc, &x, &y);
        expected ^= product;
        assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), expected);
    }
    // Accumulation is XOR, so repeating the same product cancels it.
    let x = Gf2_128::from_u128(u128::MAX);
    gf2_128_mac(&mut acc, &x, &x);
    gf2_128_mac(&mut acc, &x, &x);
    assert_eq!(gf2_128_accum_reduce(&acc).to_u128(), expected);
}

#[test]
fn conditional_moves() {
    fn check<const N: usize>() {
        use crate::runtime::algebra::limb::Limb;
        let original = core::array::from_fn::<_, N, _>(|i| (i as Limb).wrapping_mul(0x9e3779b9));
        let replacement =
            core::array::from_fn::<_, N, _>(|i| !(i as Limb).wrapping_mul(0x85ebca6b));
        let mut values = vec![0, Limb::MAX, Limb::MAX / 3, Limb::MAX / 5];
        for bit in 0..Limb::BITS {
            values.extend([1 << bit, !(1 << bit)]);
        }
        for &input_x in &values {
            for &input_y in &values {
                let (x, y) = std::hint::black_box((input_x, input_y));
                let mut result = original;
                super::cmovne(&mut result, x, y, &replacement);
                assert_eq!(result, if x != y { replacement } else { original });
                result = original;
                super::cmovnz(&mut result, x, &replacement);
                assert_eq!(result, if x != 0 { replacement } else { original });
                result = original;
                super::cmovzn(&mut result, x, &replacement);
                assert_eq!(result, if x != 0 { replacement } else { original });
            }
        }
    }
    check::<0>();
    check::<1>();
    check::<2>();
    check::<3>();
    check::<4>();
    check::<7>();
    check::<8>();
    check::<16>();
    check::<17>();
    check::<31>();
    check::<32>();
    check::<33>();
}

#[test]
fn opaque_zero_is_zero() {
    assert_eq!(super::zero_but_you_dont_know_it(), 0);
}
