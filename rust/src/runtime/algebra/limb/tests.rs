// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::algebra::arch::cmovne;

#[test]
fn test_maybe_minus_m_all_cases() {
    // Modulo M = 100 for N = 4 limbs
    // negm = 2^256 - 100
    let negm = [Limb::MAX - 99, Limb::MAX, Limb::MAX, Limb::MAX];

    // Case 1: ah = 0, ah1 = 0 (A < M, no reduction needed)
    let mut a1 = [50, 0, 0, 0];
    let ah1 = 0;
    maybe_minus_m(&mut a1, ah1, &negm);
    assert_eq!(
        a1,
        [50, 0, 0, 0],
        "Case 1 failed: ah=0, ah1=0 should keep a unchanged"
    );

    // Case 2: ah = 0, ah1 = 1 (A >= M and A < 2^256, reduction needed)
    let mut a2 = [120, 0, 0, 0];
    let ah2 = 0;
    maybe_minus_m(&mut a2, ah2, &negm);
    assert_eq!(
        a2,
        [20, 0, 0, 0],
        "Case 2 failed: ah=0, ah1=1 should subtract M"
    );

    // Case 3: ah = 1, ah1 = 0 (A >= 2^256, top carry set, reduction needed)
    // A = 2^256 + 30. Lower 4 limbs are [30, 0, 0, 0], top carry ah = 1.
    // A - M = (2^256 + 30) - 100 = 2^256 - 70.
    // Lower 4 limbs of 2^256 - 70 are [Limb::MAX - 69, Limb::MAX, Limb::MAX, Limb::MAX].
    let mut a3 = [30, 0, 0, 0];
    let ah3 = 1;
    maybe_minus_m(&mut a3, ah3, &negm);
    let expected_case3 = [Limb::MAX - 69, Limb::MAX, Limb::MAX, Limb::MAX];
    assert_eq!(
        a3, expected_case3,
        "Case 3 failed: ah=1, ah1=0 should subtract M from (2^256 + a)"
    );
}

#[test]
fn test_shr_1() {
    let a: [Limb; 2] = [0b10, 0b1];
    let shifted = shr_1(&a);
    assert_eq!(shifted, [((1 as Limb) << (LIMB_BITS - 1)) | 1, 0]);
}

#[test]
fn test_conditional_move() {
    let original = [1 as Limb, 2, 3, 4];
    let replacement = [5 as Limb, 6, 7, 8];

    let mut equal = original;
    cmovne(&mut equal, 9, 9, &replacement);
    assert_eq!(equal, original);

    let mut not_equal = original;
    cmovne(&mut not_equal, 9, 0, &replacement);
    assert_eq!(not_equal, replacement);
}
