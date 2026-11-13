// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact charges for the shared mdoc profile. The Hahn family bounds are
//! kernel-checked in Current/Parameters/Rate7.lean; these checks keep their
//! geometry and complete shared-query budgets aligned with the provider.
use num_bigint::BigUint;

use super::NEXT_PARAMETERS;

fn choose(n: usize, k: usize) -> BigUint {
    if k > n {
        return 0u32.into();
    }
    (0..k.min(n - k)).fold(1u32.into(), |x: BigUint, i| x * (n - i) / (i + 1))
}

fn natural(decimal: &[u8]) -> BigUint {
    BigUint::parse_bytes(decimal, 10).unwrap()
}

#[test]
fn shared_profile_fits_one_query_budget() {
    let p = NEXT_PARAMETERS;
    assert_eq!((p.k, p.s, p.n, p.t), (349, 12, 2443, 84));
    assert_eq!(p.n, 7 * p.k);
    let (hash_cutoff, prime_cutoff, threshold) = (865, 863, 867);
    assert!(threshold >= (p.k + 2 * p.s + 1).max(2 * p.k + p.s));
    let hash_candidates = natural(b"21898356682154715916");
    let prime_candidates = natural(b"451457457136012100305");
    let capacity = natural(b"1272737905242889781956743699885451");
    let q: BigUint = BigUint::from(1u32) << 128usize;
    let prime_order = (BigUint::from(1u32) << 256usize) - (BigUint::from(1u32) << 224usize)
        + (BigUint::from(1u32) << 192usize)
        + (BigUint::from(1u32) << 96usize)
        - 1u32;
    let denominator = choose(p.n, p.t);
    let active = choose(threshold - 1, p.t);
    let overlap = choose(p.k + 2 * p.s - 1, p.t);
    assert!(capacity <= q);
    // The u=1 discrete threshold condition for the actual active family.
    assert!(&capacity * overlap <= 2u32 * &active);

    // One shared opening pays one active threshold and both outside-list tails.
    let tails = &active + choose(hash_cutoff + p.s - 1, p.t) + choose(prime_cutoff + p.s - 1, p.t);
    assert!(1_000_000u32 * &q * tails <= 1_999_999u32 * &denominator);

    // The parent pays both rank terms and one joint active-family mass.
    // Clear denominators after scaling the complete charge by q.
    let rank_rows = choose(p.n, p.k + 2 * p.s + 1);
    let q_rank = q.pow(p.s as u32);
    let prime_rank = prime_order.pow((p.s + 1) as u32);
    let mass = &denominator + (&capacity - 1u32) * &active;
    let parent_denominator = &q_rank * &prime_rank * &prime_order * &denominator;
    let parent_numerator = &rank_rows * &prime_rank * &prime_order * &denominator
        + &q * &rank_rows * &q_rank * &prime_order * &denominator
        + (&prime_order + &q) * mass * &q_rank * &prime_rank;
    assert!(1_000_000u32 * parent_numerator <= 1_999_999u32 * parent_denominator);

    // These large committed-list caps spend part of the fingerprint role's
    // leading budget. They are not an efficient candidate-enumeration claim.
    let q_squared = q.pow(2);
    let native_squared = prime_order.pow(2);
    let fingerprint_numerator = &hash_candidates * (&hash_candidates - 1u32) * &native_squared
        + &prime_candidates * (&prime_candidates - 1u32) * &q_squared;
    let fingerprint_denominator = 2u32 * &q_squared * &native_squared;
    assert!((&q - 1u32) * fingerprint_numerator <= 2u32 * fingerprint_denominator);
    assert!(p.t > 0 && 2 * p.t < p.k);
    // Keep the formal adapter's 1024-bit source and 10-bit quotient bounds
    // tied to the circuit plan used by the development provider.
    use crate::mdoc::circuits::p256_adapter::{MASK_BITS, QUOTIENT_BITS, SHARED_BITS};
    assert_eq!((SHARED_BITS + MASK_BITS, QUOTIENT_BITS), (1024, 10));
}
