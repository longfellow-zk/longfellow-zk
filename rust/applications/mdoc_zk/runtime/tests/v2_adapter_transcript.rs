// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{SerializableField, SupportsU128Conversions, SupportsU64Conversions},
    mdoc::circuits::p256_adapter::tree,
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field},
        random::DeterministicRng,
        v2::transcript::Transcript,
    },
};

#[test]
fn rescalings_are_two_independent_nonzero_full_field_draws() {
    let p = P256Field::new();
    let mut t = Transcript::new(b"alphas");
    let mut literal = t.fork_for_test();
    let expected = literal.round(
        crate::runtime::v2::proto::RoundLabel::Conversion,
        |mut w| {
            w.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v3");
            let mut r = w.begin_squeeze();
            let a = std::array::from_fn(|_| loop {
                let a = r.elt_field(&p);
                if !p.is_zero(&a) {
                    break a;
                }
            });
            r.end_round(a)
        },
    );
    assert_eq!(alphas(&mut t.borrow(), &p), expected);
    assert_eq!(literal.u128(), t.u128());
}

#[test]
fn tree_leaves_authenticate_shared_bits_and_masked_quotients() {
    use crate::runtime::v2::sumcheck::{self, SumcheckProofGeometry};
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
        let public = public(
            &plan,
            encoded,
            &masked,
            &mut Transcript::new(b"tree").borrow(),
        )
        .unwrap();
        let c = tree::program(&plan, &sources, 0, ninput, &public).unwrap();
        let template = tree::template(&plan, &sources, 0, ninput).unwrap();
        assert_eq!(
            sumcheck::circuit_geometry(&[&c]).unwrap(),
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
        let geometry = sumcheck::circuit_geometry(&[&c]).unwrap();
        let (pads, _) = sumcheck::sample_pads(&geometry, &mut DeterministicRng::new(91), &f);
        let (proof, claim) = sumcheck::evaluate_and_prove_circuits(
            &[&c],
            inputs.clone(),
            &pads,
            &mut Transcript::new(b"tree-proof").borrow(),
            &f,
        )
        .unwrap();
        let check = sumcheck::derive_constraints_for_circuits(
            &[&c],
            &proof,
            &mut Transcript::new(b"tree-proof").borrow(),
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
        c.layers.last().unwrap().linear.for_each(|l| {
            used.insert(l.l as usize);
        });
        assert!((ninput - plan.advice_bits()..ninput).all(|i| used.contains(&i)));
        for index in [0, ninput - 1] {
            let mut bad = inputs.clone();
            f.add(&mut bad[index], &f.one());
            if index == 0 && p.is_zero(&weights[0]) {
                continue;
            }
            assert!(sumcheck::evaluate_and_prove_circuits(
                &[&c],
                bad,
                &pads,
                &mut Transcript::new(b"tree-proof").borrow(),
                &f
            )
            .is_err());
        }
    }
}

#[test]
fn conversion_binds_mu_but_not_derived_weights() {
    let p = P256Field::new();
    let a = vec![p.one(); SHARED_BITS];
    let b = vec![p.u64_to_element(3); SHARED_BITS];
    let mu = p.u64_to_element(19);
    let mut first = Transcript::new(b"derived-weights");
    let mut second = Transcript::new(b"derived-weights");
    let left = weights(&a, &p.one(), &mu, &mut first.borrow(), &p).unwrap();
    let right = weights(&b, &p.u64_to_element(7), &mu, &mut second.borrow(), &p).unwrap();
    assert_ne!(left, right);
    assert_eq!(first.bytes(32), second.bytes(32));

    let mut first = Transcript::new(b"mu-binding");
    let mut second = Transcript::new(b"mu-binding");
    weights(&a, &p.one(), &mu, &mut first.borrow(), &p).unwrap();
    weights(
        &a,
        &p.one(),
        &p.u64_to_element(20),
        &mut second.borrow(),
        &p,
    )
    .unwrap();
    assert_ne!(first.bytes(32), second.bytes(32));
}
