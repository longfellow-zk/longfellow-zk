// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! mdoc's cross-field link: shared positions of the signature inputs.
use super::*;
use crate::{core::algebra::AlgebraicField, runtime::algebra::p256::P256Field};

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
