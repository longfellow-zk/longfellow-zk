// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use num_bigint::BigUint;

use super::*;
use crate::{
    core::algebra::{SerializableField, SupportsU64Conversions},
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field, p256::P256Field},
        random::{DeterministicRng, RandomEngine},
    },
};
fn integer<P: SerializableField>(p: &P, x: &P::E) -> BigUint {
    BigUint::from_bytes_le(&p.to_bytes(x))
}
#[test]
fn advice_encoding_checks_lengths_and_unused_high_bits() {
    for bits in [2, 16, 32, 256] {
        let plan = Plan::new(vec![bits]).unwrap();
        let mut advice = vec![u8::MAX; plan.advice_bytes()];
        let used = plan.advice_bits() % 8;
        if used != 0 {
            *advice.last_mut().unwrap() = (1 << used) - 1;
        }
        assert!(plan.validate_advice(&advice).is_ok());
        assert!(plan.validate_advice(&advice[..advice.len() - 1]).is_err());
        let mut extended = advice.clone();
        extended.push(0);
        assert!(plan.validate_advice(&extended).is_err());
        if used != 0 {
            *advice.last_mut().unwrap() |= 1 << used;
            assert!(plan.validate_advice(&advice).is_err());
        }
    }
}
#[test]
fn imported_conversion_matches_independent_integer_quotients() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let modulus = BigUint::from_bytes_le(
        &MODULUS
            .iter()
            .flat_map(|x| x.to_le_bytes())
            .collect::<Vec<_>>(),
    );
    let mut rng = DeterministicRng::new(17);
    let plan = Plan::new(vec![1, 1, 256]).unwrap();
    for n in 0..8 {
        let values = [
            p.u64_to_element(n & 1),
            p.u64_to_element((n >> 1) & 1),
            rng.elt_field(&p),
        ];
        let weights = rng.elt_field_slice(3, &p);
        let target = blas::dot(&weights, &values, &p);
        let alpha = [p.u64_to_element(31), rng.elt_field(&p)];
        let encoded = plan
            .encode(&weights, &target, &alpha, Some(&values), &p, &f)
            .unwrap();
        let q = encoded.quotients.unwrap();
        for tree in 0..2 {
            let mut sum = BigUint::from(0u32);
            for ((a, value), &width) in weights.iter().zip(&values).zip(&plan.widths) {
                let a = integer(&p, &p.mulf(&alpha[tree], a));
                let value = integer(&p, value);
                for r in 0..width {
                    if value.bit(r as u64) {
                        sum += (&a << r) % &modulus;
                    }
                }
            }
            let target = integer(&p, &p.mulf(&alpha[tree], &target));
            assert_eq!(sum, &modulus * BigUint::from(q[tree]) + target);
        }
    }
}
