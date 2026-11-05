// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use num_bigint::BigUint;

use super::*;
use crate::{
    core::algebra::{SerializableField, SupportsU64Conversions},
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field, p256::P256Field},
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};
fn integer<P: SerializableField>(p: &P, x: &P::E) -> BigUint {
    BigUint::from_bytes_le(&p.to_bytes(x))
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
#[test]
fn rescalings_are_two_independent_nonzero_full_field_draws() {
    let p = P256Field::new();
    let mut t = Transcript::new(b"alphas");
    let mut literal = t.clone();
    literal.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v2");
    let expected = std::array::from_fn(|_| loop {
        let a = literal.elt_field(&p);
        if !p.is_zero(&a) {
            return a;
        }
    });
    assert_eq!(runtime::alphas(&mut t, &p), expected);
    assert_eq!(literal.u128(), t.u128());
}

#[test]
fn tree_leaves_authenticate_shared_bits_and_masked_quotients() {
    use crate::runtime::sumcheck_v2::{self, SumcheckProofGeometry};
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let plan = Plan::new(vec![1, 256]).unwrap();
    let ninput = plan.bits + plan.advice_bits();
    let sources: Vec<_> = (0..plan.bits).collect();
    let values = [p.one(), p.u64_to_element(12345)];
    // Include the exceptional power=1 case: its two linear terms cancel,
    // rather than turning into an LFC3 assertion marker.
    for weights in [[p.u64_to_element(42), p.one()], [p.zero(), p.zero()]] {
        let target = blas::dot(&weights, &values, &p);
        let encoded = plan
            .encode(
                &weights,
                &target,
                &[p.u64_to_element(17), p.u64_to_element(31)],
                Some(&values),
                &p,
                &f,
            )
            .unwrap();
        let q = encoded.quotients.unwrap();
        let mut masked = vec![0; plan.advice_bytes()];
        for r in 0..plan.advice_bits() {
            masked[r / 8] |= (((q[r / plan.quotient_bits] >> (r % plan.quotient_bits)) as u8 & 1)
                ^ 1)
                << (r % 8);
        }
        let public =
            runtime::public(&plan, encoded, &masked, &mut Transcript::new(b"tree")).unwrap();
        let c = tree::program(&plan, &sources, 0, ninput, &public).unwrap();
        let template = tree::template(&plan, &sources, 0, ninput).unwrap();
        assert_eq!(
            SumcheckProofGeometry::from_circuit(&c),
            SumcheckProofGeometry::from_circuit(&template)
        );
        let mut inputs = Vec::new();
        for (value, &width) in values.iter().zip(&plan.widths) {
            let b = p.to_bytes(value);
            inputs.extend(
                (0..width).map(|r| f.u128_to_element(u128::from((b[r / 8] >> (r % 8)) & 1))),
            );
        }
        inputs.extend(vec![f.one(); plan.advice_bits()]);
        let geometry = SumcheckProofGeometry::from_circuit(&c);
        let (pads, _) = sumcheck_v2::sample_pads(&geometry, &mut DeterministicRng::new(91), &f);
        let (proof, claim) = sumcheck_v2::evaluate_and_prove_circuits(
            &[&c],
            inputs.clone(),
            &pads,
            &mut Transcript::new(b"tree-proof"),
            &f,
        )
        .unwrap();
        let check = sumcheck_v2::derive_constraints_for_circuits(
            &[&c],
            &proof,
            &mut Transcript::new(b"tree-proof"),
            &f,
        )
        .unwrap();
        assert_eq!(claim, check);
        assert!(check
            .residuals(&inputs, &pads, &f)
            .unwrap()
            .iter()
            .all(|x| f.is_zero(x)));
        let mut used = std::collections::BTreeSet::new();
        c.raw.layers.last().unwrap().linear.for_each(|l| {
            used.insert(l.l as usize);
        });
        assert!((ninput - plan.advice_bits()..ninput).all(|i| used.contains(&i)));
        for index in [0, ninput - 1] {
            let mut bad = inputs.clone();
            f.add(&mut bad[index], &f.one());
            if index == 0 && p.is_zero(&weights[0]) {
                continue;
            }
            assert!(sumcheck_v2::evaluate_and_prove_circuits(
                &[&c],
                bad,
                &pads,
                &mut Transcript::new(b"tree-proof"),
                &f
            )
            .is_err());
        }
    }
}
