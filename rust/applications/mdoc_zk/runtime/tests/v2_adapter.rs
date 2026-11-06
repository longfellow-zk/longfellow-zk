// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{self, Circuit, Layer, Linear, RawCircuit, Stream},
    },
    runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, RuntimeField},
        random::DeterministicRng,
        v2::{polygero::PolygeroConfig, transcript::Transcript, zk::ZkContext},
    },
};

#[test]
fn binary_source_positions_match_native_shared_inputs() {
    use crate::{
        core::algebra::{SerializableField, SupportsNatConversions},
        mdoc::{
            circuits::{p256_adapter, parse_test_data},
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
    let mask = f.u64_to_element(1234567);
    let plan = p256_adapter::shared_plan();
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
        let mut private = inputs::push_witness_hash(&attrs, &parsed).unwrap();
        let bytes = f.to_bytes(&mask);
        private.extend((0..256).map(|r| (bytes[r / 8] >> (r % 8)) & 1 != 0));
        private.resize(private.len() + plan.advice_bits(), true);
        let positions = binary::sources(public.len(), public.len() + private.len()).unwrap();
        let mut expected = inputs::push_witness_sig(&f, &q, &curve, &issuer_pk, &parsed).unwrap();
        expected.truncate(p256_adapter::SHARED_BITS);
        expected.extend((0..256).map(|r| {
            if (bytes[r / 8] >> (r % 8)) & 1 != 0 {
                f.one()
            } else {
                f.zero()
            }
        }));
        let actual: Vec<_> = positions
            .iter()
            .map(|&i| {
                if private[i - public.len()] {
                    f.one()
                } else {
                    f.zero()
                }
            })
            .collect();
        assert_eq!(actual, expected);
        assert!(positions
            .iter()
            .all(|&i| i < public.len() + private.len() - plan.advice_bits()));
    }
}
#[test]
fn native_shared_prefix_and_every_linear_check_are_authenticated() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
    let raw = RawCircuit {
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
    };
    let c = Circuit {
        id: v2::compute_id(&f, &raw),
        raw,
    };
    let part = SharedParticipant::new(
        &c,
        1,
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
        &ctx,
    )
    .unwrap();
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
    assert_eq!(witness[..2], [native, mask]);
    assert_eq!(
        witness.len(),
        2 + part.geometry().sc_geom.pad_count().unwrap()
    );
    let mut tp = Transcript::new(b"native-rows");
    let mut tv = tp.fork_for_test();
    let reduction = part.reduce(&c, &[f.one()], state, &mut tp, &f).unwrap();
    let checked = part
        .reduce_verify(&c, &[f.one()], &reduction.proof, &mut tv, &f)
        .unwrap();
    assert_eq!(reduction.claim.weights, checked.weights);
    assert_eq!(reduction.claim.target, checked.target);
    let eta = f.u64_to_element(19);
    let mu = reduction.masked_value(&eta, &f);
    let statement = part.finish(reduction.claim, &eta, &mu, &f).unwrap();
    let residual = |a: &crate::runtime::v2::polygero::LinearStatement<_>, w: &[_]| {
        let mut x = a.b[0];
        for t in &a.a {
            f.fma(&mut x, &t.k, &w[t.w]);
        }
        x
    };
    assert!(f.is_zero(&residual(&statement, &witness)));
    let pad = statement
        .a
        .iter()
        .find(|a| a.w >= 2 && !f.is_zero(&a.k))
        .unwrap()
        .w;
    let mut bad = witness.clone();
    f.add(&mut bad[pad], &f.one());
    assert!(!f.is_zero(&residual(&statement, &bad)));
    let mut forged = reduction.proof;
    f.add(&mut forged.layers[0].cross, &f.one());
    let mut t = Transcript::new(b"native-rows");
    let claim = part
        .reduce_verify(&c, &[f.one()], &forged, &mut t, &f)
        .unwrap();
    let mu = f.addf(&f.mulf(&eta, &f.mulf(&claim.weights[0], &source)), &mask);
    let statement = part.finish(claim, &eta, &mu, &f).unwrap();
    assert!(!f.is_zero(&residual(&statement, &witness)));
}
