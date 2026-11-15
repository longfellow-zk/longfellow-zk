// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Fixed-limb integer witnesses. Runtime roles do not depend on num-bigint.
/// A 256-bit unsigned integer, little-endian limbs.
pub(crate) type Int256 = [u64; 4];
/// P-256 coordinate modulus, little-endian limbs. The scalar order differs.
const MODULUS: [u64; 4] = [
    0xffffffffffffffff,
    0x00000000ffffffff,
    0,
    0xffffffff00000001,
];

/// `floor(2^512 / p)`, little-endian limbs.
pub(crate) const RECIPROCAL: [u64; 5] = [
    0x0000000000000003,
    0xfffffffeffffffff,
    0xfffffffefffffffe,
    0x00000000ffffffff,
    0x0000000000000001,
];

#[cfg(any(test, feature = "prover"))]
pub(crate) fn bit(a: &Int256, r: usize) -> bool {
    (a[r / 64] >> (r % 64)) & 1 != 0
}

/// Whether a canonical unsigned integer fits in the group's bit width.
#[cfg(any(test, feature = "prover"))]
pub(crate) fn fits_width(value: &Int256, width: usize) -> bool {
    assert!(width <= 256);
    let (whole, remaining) = (width / 64, width % 64);
    if remaining == 0 {
        value[whole..].iter().all(|&limb| limb == 0)
    } else {
        value[whole] >> remaining == 0 && value[whole + 1..].iter().all(|&limb| limb == 0)
    }
}

pub(crate) fn at_least_p(a: &[u64; 5]) -> bool {
    a[4] != 0
        || (0..4)
            .rev()
            .find_map(|i| (a[i] != MODULUS[i]).then_some(a[i] > MODULUS[i]))
            .unwrap_or(true)
}

/// The 4x5-limb product.
fn mul_wide(a: &Int256, b: &[u64; 5]) -> [u64; 9] {
    let mut out = [0u64; 9];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = u128::from(x) * u128::from(y) + u128::from(out[i + j]) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    out
}

/// The first 256 binary digits of `a / p` for `a < p`: the integer
/// `floor(a * 2^256 / p)`.
///
/// Doubling `a_r` modulo p subtracts p exactly when `2 a_r >= p`, where
/// `a_r = a * 2^r mod p`: these corrections are the digits of `a / p` by
/// long division, so correction `r` is bit `255 - r` of the result.
///
/// Barrett's estimate `floor(a * floor(2^512 / p) / 2^256)` is the result or
/// one less: one comparison of the remainder with p decides.
pub(crate) fn fraction_digits(a: &Int256) -> Int256 {
    let t = mul_wide(a, &RECIPROCAL);
    let mut q = [t[4], t[5], t[6], t[7]];
    // r = a * 2^256 - q * p lies in [0, 2p), so its low five limbs suffice.
    let qp = mul_wide(&q, &[MODULUS[0], MODULUS[1], MODULUS[2], MODULUS[3], 0]);
    let mut r = [0u64; 5];
    let mut borrow = 0u64;
    for (i, ri) in r.iter_mut().enumerate() {
        let x = if i < 4 { 0 } else { a[0] };
        let (difference, b0) = x.overflowing_sub(qp[i]);
        let (reduced_difference, b1) = difference.overflowing_sub(borrow);
        *ri = reduced_difference;
        borrow = u64::from(b0 | b1);
    }
    if at_least_p(&r) {
        let mut carry = 1u64;
        for limb in &mut q {
            let (s, c) = limb.overflowing_add(carry);
            *limb = s;
            carry = u64::from(c);
        }
    }
    q
}

pub(crate) fn reduce_exponent(word: Int256) -> u128 {
    let low = u128::from(word[0]) | (u128::from(word[1]) << 64);
    let high = u128::from(word[2]) | (u128::from(word[3]) << 64);
    let (sum, carry) = low.overflowing_add(high);
    let (folded, carry2) = sum.overflowing_add(u128::from(carry));
    let reduced = folded + u128::from(carry2);
    if reduced == u128::MAX {
        0
    } else {
        reduced
    }
}
