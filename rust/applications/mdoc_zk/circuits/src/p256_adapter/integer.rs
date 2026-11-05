// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Fixed-limb integer witnesses. Runtime roles do not depend on num-bigint.
pub(crate) type Word = [u64; 4];
use super::MODULUS;

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn bit(a: &Word, r: usize) -> bool {
    (a[r / 64] >> (r % 64)) & 1 != 0
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn add_word(a: &mut [u64; 5], b: &Word) {
    let mut carry = 0u128;
    for i in 0..4 {
        carry += u128::from(a[i]) + u128::from(b[i]);
        a[i] = carry as u64;
        carry >>= 64;
    }
    a[4] = a[4]
        .checked_add(carry as u64)
        .expect("adapter sum overflow");
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn subtract_word(a: &mut [u64; 5], b: &Word) -> bool {
    let mut borrow = false;
    for i in 0..5 {
        let (x, b0) = a[i].overflowing_sub(if i < 4 { b[i] } else { 0 });
        let (x, b1) = x.overflowing_sub(u64::from(borrow));
        a[i] = x;
        borrow = b0 || b1;
    }
    !borrow
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn at_least_p(a: &[u64; 5]) -> bool {
    a[4] != 0
        || (0..4)
            .rev()
            .find_map(|i| (a[i] != MODULUS[i]).then_some(a[i] > MODULUS[i]))
            .unwrap_or(true)
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn double(a: &mut Word) -> bool {
    let mut wide = [0; 5];
    for i in 0..4 {
        wide[i] |= a[i] << 1;
        wide[i + 1] = a[i] >> 63;
    }
    let correction = at_least_p(&wide);
    if correction {
        assert!(subtract_word(&mut wide, &MODULUS));
    }
    *a = wide[..4].try_into().unwrap();
    correction
}

/// Long division by the P256 prime. Quotient width follows the numerator.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn divide<const N: usize>(value: &[u64; N]) -> ([u64; N], Word) {
    let mut quotient = [0; N];
    let mut remainder = [0u64; 5];
    for r in (0..64 * N).rev() {
        for i in (0..5).rev() {
            remainder[i] = (remainder[i] << 1)
                | if i == 0 {
                    (value[r / 64] >> (r % 64)) & 1
                } else {
                    remainder[i - 1] >> 63
                };
        }
        if at_least_p(&remainder) {
            assert!(subtract_word(&mut remainder, &MODULUS));
            quotient[r / 64] |= 1u64 << (r % 64);
        }
    }
    (quotient, remainder[..4].try_into().unwrap())
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn reduce_exponent(word: Word) -> u128 {
    let low = u128::from(word[0]) | (u128::from(word[1]) << 64);
    let high = u128::from(word[2]) | (u128::from(word[3]) << 64);
    let (sum, carry) = low.overflowing_add(high);
    let (sum, carry2) = sum.overflowing_add(u128::from(carry));
    let sum = sum + u128::from(carry2);
    if sum == u128::MAX {
        0
    } else {
        sum
    }
}
