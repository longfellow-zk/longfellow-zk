// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! mdoc's cross-field link: shared positions and the mixed split.
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{Circuit, Layer, Linear, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, RuntimeField},
        random::DeterministicRng,
        v2::{
            foreign::{
                mixed::MixedParticipant,
                storage::{Group, StorageMap},
            },
            polygero::{LinearStatement, PolygeroConfig},
            transcript::Transcript,
            zk::ZkContext,
        },
    },
};

#[test]
fn shared_positions_match_signature_inputs() {
    use crate::{
        core::algebra::SupportsNatConversions,
        mdoc::{
            circuits::{p256_adapter::SHARED_BITS, parse_test_data},
            runtime::v2::{inputs, req_attr},
        },
        runtime::algebra::{secp256r1::Secp256r1, Q256Field, RuntimeNat},
    };
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let fixture = &crate::mdoc::testcases::vectors::TEST_DATA;
    let (issuer, parsed, now) = parse_test_data::<4, RuntimeNat<4>>(fixture);
    let issuer_pk = (f.reduce_nat(&issuer.0), f.reduce_nat(&issuer.1));
    for count in 1..=4 {
        let attrs: Vec<_> = parsed
            .attrs
            .iter()
            .cycle()
            .take(count)
            .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
            .collect();
        let public =
            inputs::push_input_hash(&attrs, now.as_bytes(), false, fixture.doc_type.as_bytes());
        let private = inputs::push_witness_hash(&attrs, &parsed).unwrap();
        let width = public.len() + private.len();
        let positions = shared_positions(public.len(), width).unwrap();
        let mut expected = inputs::push_witness_sig(&f, &q, &curve, &issuer_pk, &parsed).unwrap();
        expected.truncate(SHARED_BITS);
        let actual: Vec<_> = positions
            .iter()
            .map(|&i| {
                assert!(i < width, "shared values lie inside the hash inputs");
                if private[i - public.len()] {
                    f.one()
                } else {
                    f.zero()
                }
            })
            .collect();
        assert_eq!(actual, expected);
    }
}

#[test]
fn mixed_split_authenticates_native_rows_and_foreign_values() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let ctx = ZkContext::new(&domain);
    let raw = RawCircuitBuilder {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.zero()],
        layers: vec![Layer::with_assertions(
            3,
            Stream::default(),
            Stream::<Linear>::from_terms([Linear { g: 0, l: 2, k: 0 }]),
            Stream::default(),
            |_| true,
        )],
    }
    .build();
    let c = Circuit::from_raw(&f, raw);
    // Value 0 (the first private input) lives in the binary commitment.
    let shared = Group { start: 7, width: 1 };
    let mask_group = Group {
        start: 20,
        width: 256,
    };
    let values = crate::runtime::v2::foreign::frontend::value_count(&c).unwrap();
    let storage = StorageMap::new(values, &[(0, shared)]).unwrap();
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let part = MixedParticipant::new(&c, storage, mask_group, config, &ctx).unwrap();
    let source = f.one();
    let native = f.zero();
    let mask = f.u64_to_element(17);
    let (state, witness) = part
        .prepare(
            &c,
            vec![source, native],
            mask,
            &mut DeterministicRng::new(42),
            &f,
        )
        .unwrap();
    // Native cells: the native private input, then R, then the pads.
    assert_eq!(witness[0], native);
    assert_eq!(witness[1], mask);
    assert_eq!(
        witness.len(),
        2 + part.geometry().sc_geom.pad_count().unwrap()
    );
    let mut tp = Transcript::new(b"mixed-rows");
    let mut tv = tp.fork_for_test();
    let reduction = part
        .prove(&c, &[f.one()], state, &mut tp.borrow(), &f)
        .unwrap();
    let checked = part
        .reduce(&c, &[f.one()], &reduction.proof, &mut tv.borrow(), &f)
        .unwrap();
    assert_eq!(reduction.claim.weights, checked.weights);
    assert_eq!(reduction.claim.target, checked.target);
    let eta = f.u64_to_element(19);
    let mu = reduction.masked_value(&part, &eta, &f);
    // Foreign claim: eta*w_0*source + R = mu, over the shared group and R.
    let foreign = part.foreign_claim(&checked, &eta, &mu, &f).unwrap();
    assert_eq!(foreign.terms.len(), 2);
    assert_eq!(
        (foreign.terms[0].0, foreign.terms[1].0),
        (shared, mask_group)
    );
    let values = reduction.foreign_values(&part);
    let mut sum = f.zero();
    for ((_, k), v) in foreign.terms.iter().zip(&values) {
        f.fma(&mut sum, k, v);
    }
    assert_eq!(sum, foreign.target);
    let residual = |a: &LinearStatement<_>, w: &[_]| {
        let mut x = a.b[0];
        for t in &a.a {
            f.fma(&mut x, &t.k, &w[t.w]);
        }
        x
    };
    let statement = part.native_statement(&checked, &eta, &mu, &f).unwrap();
    assert!(f.is_zero(&residual(&statement, &witness)));
    // Every native pad cell is authenticated.
    let pad = statement
        .a
        .iter()
        .find(|a| a.w >= 2 && !f.is_zero(&a.k))
        .unwrap()
        .w;
    let mut bad = witness.clone();
    f.add(&mut bad[pad], &f.one());
    assert!(!f.is_zero(&residual(&statement, &bad)));
    // A forged sumcheck message changes the claim; the honest split fails.
    let mut forged = reduction.proof;
    f.add(&mut forged.layers[0].cross, &f.one());
    let mut t = Transcript::new(b"mixed-rows");
    let claim = part
        .reduce(&c, &[f.one()], &forged, &mut t.borrow(), &f)
        .unwrap();
    let mu = f.addf(&f.mulf(&eta, &f.mulf(&claim.weights[0], &source)), &mask);
    let statement = part.native_statement(&claim, &eta, &mu, &f).unwrap();
    assert!(!f.is_zero(&residual(&statement, &witness)));
}
