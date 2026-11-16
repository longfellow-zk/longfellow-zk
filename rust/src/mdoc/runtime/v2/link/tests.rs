// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! mdoc's cross-field link: shared positions of the signature inputs.
use crate::{
    core::algebra::AlgebraicField,
    mdoc::{testcases::TEST_DATA, v2::link::*},
    runtime::algebra::p256::P256Field,
};

#[test]
fn shared_positions_match_signature_inputs() {
    use crate::{
        mdoc::{
            cbor::test_utils::parse_test_data,
            proto::layout::SHARED_BITS,
            runtime::tests::specs::v2_spec,
            v2::{inputs, req_attr, request::Request},
        },
        runtime::algebra::{q256::Q256Field, secp256r1::Secp256r1, RuntimeNat},
    };
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let fixture = &TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, RuntimeNat<4>>(fixture);
    for count in 1..=4 {
        let attrs: Vec<_> = parsed
            .attrs
            .iter()
            .cycle()
            .take(count)
            .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
            .collect();
        let mut spec = v2_spec();
        spec.num_attributes = count;
        let request = Request::check(
            &spec,
            fixture.pkx,
            fixture.pky,
            fixture.transcript,
            &attrs,
            now,
            fixture.doc_type,
            &f,
        )
        .unwrap();
        let derived = inputs::PublicInputs::derive(&request, &f);
        let public = derived.hash();
        let private = inputs::push_witness_hash(&request, &parsed).unwrap();
        let width = public.len() + private.len();
        let positions = shared_positions(public.len(), width).unwrap();
        let mut expected = inputs::push_witness_sig(&f, &q, &curve, &request, &parsed).unwrap();
        expected.truncate(SHARED_BITS);
        assert!(positions
            .iter()
            .enumerate()
            .all(|(k, &(value, _))| value == k));
        let actual: Vec<_> = positions
            .iter()
            .map(|&(_, i)| {
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
