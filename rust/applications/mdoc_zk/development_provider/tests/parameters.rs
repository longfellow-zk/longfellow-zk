// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact numerical charges for the shared mdoc profile. This checks parameter
//! arithmetic; it does not extend the earlier full application Lean certificate.
use num_bigint::BigUint;

use super::NEXT_PARAMETERS;
use crate::runtime::proto::polygero::PolygeroConfig;

fn choose(n: usize, k: usize) -> BigUint {
    if k > n {
        return 0u32.into();
    }
    (0..k.min(n - k)).fold(1u32.into(), |x: BigUint, i| x * (n - i) / (i + 1))
}

/// The interleaved Johnson bound for agreement c and pairwise overlap d-1.
/// These are analysis cutoffs, not parameters transmitted in the protocol.
fn list_bound(n: usize, c: usize, d: usize) -> usize {
    assert!(c <= n && d <= c);
    let denominator = c * c - n * (d - 1);
    assert!(denominator > 0);
    n * (c - d + 1) / denominator
}

fn rank_ok(p: PolygeroConfig) -> bool {
    let q: BigUint = BigUint::from(1u32) << 128usize;
    4u32 * choose(p.n, p.k + 2 * p.s + 1) <= q.pow(p.s as u32)
}

fn charges(p: PolygeroConfig) -> (BigUint, BigUint) {
    let (hash_cutoff, native_cutoff, threshold) = (1015, 994, 1025);
    assert!(threshold >= (p.k + 2 * p.s + 1).max(2 * p.k + p.s));
    let hash_candidates = list_bound(p.n, hash_cutoff, p.k);
    let native_candidates = list_bound(p.n, native_cutoff, p.k);
    let capacity = list_bound(p.n, threshold, p.k + 2 * p.s);
    assert_eq!(
        (hash_candidates, native_candidates, capacity),
        (32, 207, 439)
    );
    let q: BigUint = BigUint::from(1u32) << 128usize;
    let denominator = choose(p.n, p.t);
    let query_units = |cutoff: usize| -> BigUint {
        let numerator = &q * choose((threshold - 1).max(cutoff + p.s - 1), p.t);
        (numerator + &denominator - 1u32) / &denominator
    };
    // One query set serves both fields. A union bound adds these tails; neither
    // independence nor the smaller of the two failure probabilities is used.
    let shared_query = query_units(hash_cutoff) + query_units(native_cutoff);
    let coefficient = shared_query
        .clone()
        .max(BigUint::from(capacity + 1))
        .max(BigUint::from(2 * hash_candidates + 1))
        + 1u32;
    // Binary frontend: at most 593 ordinary units, 20 nonzero terminal scales,
    // and one packing check. 2*20*q/(q-1)<41 gives 635 units per candidate.
    // One further unit covers the P256 terms, even after multiplying by the
    // two committed-list sizes, and the two-rescaling conversion error.
    let constant = BigUint::from(635 * hash_candidates + capacity + 1) + shared_query + 1u32;
    // The native candidate family and all native challenges use q>=2^255.
    // Their conservative 2^24/q charge is less than one binary-field unit.
    assert!(hash_candidates * native_candidates < 1 << 14);
    assert!(2 * hash_candidates * native_candidates * (593 + 40 + 4) < 1 << 24);
    assert!((BigUint::from(1u32) << 25) * &q < (BigUint::from(1u32) << 255));
    // For fixed false source bits, the integer difference after one scaling
    // lies in an interval of length at most 2048*p. Its multiples of 2^128-1
    // give a per-scaling bound below 8192/(2^128-1). The two scalings form one
    // challenge block: no message is sent between them. Their squared bound,
    // unioned over both committed lists, consumes less than half a field unit.
    let plan = crate::mdoc::circuits::p256_adapter::shared_plan();
    assert_eq!((plan.bits, plan.quotient_bits), (1024, 10));
    let group_order = &q - 1u32;
    let conversion = BigUint::from(hash_candidates * native_candidates) << 26usize;
    assert!(2u32 * &q * conversion < &group_order * &group_order);
    (coefficient, constant)
}

#[test]
fn shared_profile_retains_the_work_normalized_numerical_budget() {
    assert!(NEXT_PARAMETERS.t > 0 && 2 * NEXT_PARAMETERS.t < NEXT_PARAMETERS.k);
    assert!(rank_ok(NEXT_PARAMETERS));
    let (coefficient, constant) = charges(NEXT_PARAMETERS);
    assert_eq!(coefficient, 1918u32.into());
    assert_eq!(constant, 22678u32.into());
    // In units of 2^-128, a 116-bit work coefficient is 4096. With at least 8
    // Merkle queries, the startup allowance is 9*4096. Strict slack covers the
    // one-tree SHA256 term for n <= 8192 and at most 1204 protocol slots.
    assert!(coefficient < 4096u32.into());
    assert!(coefficient + constant < (9u32 * 4096 - 1).into());
    assert!(2 * NEXT_PARAMETERS.n <= 16384);
}

#[test]
fn one_fewer_query_or_masking_degree_exceeds_the_budget() {
    let mut p = NEXT_PARAMETERS;
    p.t -= 1;
    let (coefficient, constant) = charges(p);
    assert!(coefficient >= 4096u32.into() || coefficient + constant >= (9u32 * 4096 - 1).into());
    p = NEXT_PARAMETERS;
    p.s -= 1;
    assert!(!rank_ok(p));
}
