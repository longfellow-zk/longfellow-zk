// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn rational_signs_and_floor() {
    assert_eq!(Q::new(2.into(), (-4).into()), Q::new((-1).into(), 2.into()));
    assert_eq!(Q::new((-3).into(), 2.into()).floor(), BigInt::from(-2));
    assert_eq!(Q::ratio(1, 3).add(&Q::ratio(1, 6)), Q::ratio(1, 2));
    assert_eq!(Q::ratio(7, 9).div(&Q::ratio(14, 3)), Q::ratio(1, 6));
}
#[test]
fn binomial_matches_pascal() {
    let mut row = vec![BigInt::one()];
    for n in 0..40 {
        for (r, v) in row.iter().enumerate() {
            assert_eq!(&choose(n, r), v);
        }
        let mut next = vec![BigInt::one(); row.len() + 1];
        for r in 1..row.len() {
            next[r] = &row[r - 1] + &row[r];
        }
        row = next;
    }
    assert_eq!(choose(4, 5), BigInt::zero());
}
