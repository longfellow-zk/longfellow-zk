// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Wrapping-mode (P-256) adapter: challenges, bindings, and tree authentication
//! of the claim's bits and masked quotients through the fixed fragment.
use super::{
    adapter::{
        fragment,
        p256::{absorb_masked, conversion, P256Plan},
        virtual_inputs,
    },
    word::{MaskedWord, Otp},
};
use crate::{
    core::algebra::{AlgebraicField, SerializableField, SupportsU128Conversions},
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field, p256::P256Field},
        random::DeterministicRng,
        v2::{
            proto::RoundLabel,
            sumcheck,
            transcript::Transcript,
            zk::{
                split::transcript::absorb_mu,
                storage::{Group, ModularClaim, ReservedSuffix},
            },
        },
    },
};

#[test]
fn conversion_draws_two_independent_nonzero_full_field_challenges() {
    let p = P256Field::new();
    let mut t = Transcript::new(b"alphas");
    let mut literal = t.fork_for_test();
    let expected = literal.round(RoundLabel::Conversion, |mut w| {
        w.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v3");
        let mut r = w.begin_squeeze();
        let a = std::array::from_fn(|_| loop {
            let a = r.elt_field(&p);
            if !p.is_zero(&a) {
                break a;
            }
        });
        r.end_round(a)
    });
    assert_eq!(conversion(&mut t.borrow(), &p), expected);
    assert_eq!(literal.u128(), t.u128());
}

#[test]
fn mu_is_bound_and_derived_claims_are_not_absorbed() {
    use crate::core::algebra::SupportsU64Conversions;
    let p = P256Field::new();
    let mu = p.u64_to_element(19);
    let state = |mu: &_| {
        let mut t = Transcript::new(b"mu-binding");
        absorb_mu(&mut t.borrow(), mu, &p);
        t.bytes(32)
    };
    assert_eq!(state(&mu), state(&mu));
    assert_ne!(state(&mu), state(&p.u64_to_element(20)));
}

#[test]
fn masked_quotients_are_bound() {
    let mut rng = DeterministicRng::new(3);
    let pad = Otp::<10>::sample(&mut rng);
    let word = |k| {
        MaskedWord::mask(
            crate::runtime::v2::foreign::word::Word::<10>::new(k).unwrap(),
            &pad,
        )
    };
    let state = |m: [MaskedWord<10>; 2]| {
        let mut t = Transcript::new(b"advice-binding");
        absorb_masked(&mut t.borrow(), &m);
        t.bytes(32)
    };
    // Either word changes the state; so does their order.
    let base = state([word(0), word(5)]);
    assert_ne!(base, state([word(1), word(5)]), "first word not bound");
    assert_ne!(base, state([word(0), word(4)]), "second word not bound");
    assert_ne!(base, state([word(5), word(0)]), "word order not bound");
}

/// The tree's leaves authenticate every claim bit and every quotient pad bit.
/// Includes the exceptional weight-zero claim, whose leaves have power one.
#[test]
fn tree_leaves_authenticate_claim_bits_and_masked_quotients() {
    use crate::core::algebra::SupportsU64Conversions;
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    const Q: usize = 9;
    let plan = P256Plan::<Q>::new(vec![1, 256]).unwrap();
    let groups = [
        Group { start: 0, width: 1 },
        Group {
            start: 1,
            width: 256,
        },
    ];
    let mut suffix = ReservedSuffix::new(257);
    let otp = [suffix.word::<Q>(), suffix.word::<Q>()];
    let values = [p.one(), p.u64_to_element(12345)];
    let mut rng = DeterministicRng::new(91);
    let pads = [Otp::<Q>::sample(&mut rng), Otp::<Q>::sample(&mut rng)];
    for weights in [[p.u64_to_element(42), p.one()], [p.zero(), p.zero()]] {
        let claim = ModularClaim {
            terms: groups
                .iter()
                .copied()
                .zip(weights.iter().cloned())
                .collect(),
            target: blas::dot(&weights, &values, &p),
        };
        let alpha = [p.u64_to_element(17), p.u64_to_element(31)];
        let encoded = plan.encode(&claim, &alpha, Some(&values), &p, &f).unwrap();
        let q = encoded.quotients.unwrap();
        let masked = [
            MaskedWord::mask(q[0], &pads[0]),
            MaskedWord::mask(q[1], &pads[1]),
        ];
        let shape = plan.shape();
        let leaves = virtual_inputs(shape, encoded.trees(&claim, &otp, &masked, &f), &f).unwrap();
        let c = fragment(0, suffix.end(), shape).unwrap();
        // Committed bits: the claim's values, then both quotient pads.
        let mut committed = Vec::new();
        for (value, g) in values.iter().zip(&groups) {
            let b = p.to_bytes(value);
            committed.extend(
                (0..g.width).map(|r| f.u128_to_element(u128::from((b[r / 8] >> (r % 8)) & 1))),
            );
        }
        let mut reserved = suffix.witness();
        for (g, pad) in otp.iter().zip(&pads) {
            reserved.set(g.group(), pad.bits()).unwrap();
        }
        committed.extend(
            reserved
                .into_bits()
                .into_iter()
                .map(|b| f.u128_to_element(u128::from(b))),
        );
        let with_leaves = |committed: &[_]| {
            let mut inputs = committed.to_vec();
            for e in &leaves.entries {
                inputs.push(f.addf(&e.constant, &f.mulf(&e.coefficient, &committed[e.source])));
            }
            inputs
        };
        let inputs = with_leaves(&committed);
        let geometry = sumcheck::circuit_geometry(&[&c]).unwrap();
        let (pads_sc, _) = sumcheck::sample_pads(&geometry, &mut DeterministicRng::new(5), &f);
        let (proof, claim_sc) = sumcheck::evaluate_and_prove_circuits(
            &[&c],
            inputs.clone(),
            &pads_sc,
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
        assert_eq!(claim_sc, check);
        assert!(check
            .residuals(&inputs, &pads_sc, &f)
            .unwrap()
            .iter()
            .all(|x| f.is_zero(x)));
        // A changed claim bit (when its weight is nonzero) or quotient pad bit
        // changes some leaf, and the tree product is no longer one.
        for index in [0, committed.len() - 1] {
            if index == 0 && p.is_zero(&weights[0]) {
                continue;
            }
            let mut bad = committed.clone();
            f.add(&mut bad[index], &f.one());
            assert!(sumcheck::evaluate_and_prove_circuits(
                &[&c],
                with_leaves(&bad),
                &pads_sc,
                &mut Transcript::new(b"tree-proof").borrow(),
                &f
            )
            .is_err());
        }
    }
}
