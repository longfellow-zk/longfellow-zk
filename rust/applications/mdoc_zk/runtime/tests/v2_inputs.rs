// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! V2 input capacity and early rejection, without compiling a circuit.
use crate::{
    mdoc::v2::{
        req_attr, run_mdoc_prover_inner, run_mdoc_verifier, MdocProverErrorCode,
        MdocVerifierErrorCode,
    },
    runtime::random::DeterministicRng,
};

#[test]
fn namespace_capacity_and_encoding_are_checked_before_proving() {
    use crate::mdoc::proto::hash::constants::K_NAMESPACE_BYTES;
    let spec = &crate::mdoc::runtime::tests_specs::v2_spec();
    for namespace in [vec![], vec![b'n'; K_NAMESPACE_BYTES + 1], vec![0xff]] {
        let attrs = [req_attr(namespace, "a", [0xf5])];
        let mut rng = DeterministicRng::new(42);
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                b"inputs",
                &attrs,
                "2026-10-23T00:00:00Z",
                "doc",
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput)
        );
        assert_eq!(rng.state, 42);
        assert_eq!(
            run_mdoc_verifier(
                spec,
                &[],
                "0",
                "0",
                b"inputs",
                &attrs,
                "2026-10-23T00:00:00Z",
                "doc",
                &[],
            ),
            Err(MdocVerifierErrorCode::InvalidInput)
        );
    }
    assert!(super::public_inputs_fit(
        &[req_attr(vec![b'n'; K_NAMESPACE_BYTES], "a", [0xf5])],
        b"2026-10-23T00:00:00Z",
        b"doc",
    ));
}

#[test]
fn global_namespace_scopes_the_honest_attribute_lookup() {
    use crate::{mdoc::circuits::cbor::mdoc::parse_mdoc, runtime::algebra::RuntimeNat};
    let fixture = &crate::mdoc::testcases::vectors::DHS_COMPLIANCE_MDOC_10;
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let namespaces = parsed.namespaces().unwrap();
    let attribute = &parsed.attrs[0];
    let actual = namespaces
        .iter()
        .find(|namespace| {
            namespace
                .digest_range
                .contains(&attribute.mso_digest_offset_in_preimage)
        })
        .unwrap();
    assert_eq!(actual.name, b"org.iso.18013.5.1.aamva");
    let request = [req_attr(
        &actual.name,
        &attribute.name,
        &attribute.cbor_value,
    )];
    let expected = super::push_witness_hash(&request, &parsed).unwrap();
    let other = namespaces
        .iter()
        .find(|namespace| namespace.name != actual.name)
        .unwrap();
    let mut duplicate = attribute.clone();
    duplicate.mso_digest_offset_in_preimage = other.digest_range.start;
    duplicate.cbor_issuer_signed_item[20] ^= 1;
    let mut with_duplicate = parsed.clone();
    with_duplicate.attrs.insert(0, duplicate);
    assert_eq!(
        super::push_witness_hash(&request, &with_duplicate).unwrap(),
        expected,
        "a matching name in a different namespace must not shadow the selected attribute"
    );
    let wrong = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    assert_eq!(
        super::push_witness_hash(&wrong, &parsed),
        Err(MdocProverErrorCode::AttributeNotFound)
    );
}

#[test]
fn zero_signature_is_a_witness_error() {
    use crate::{
        core::algebra::{AlgebraicField, Nat},
        mdoc::circuits::cbor::mdoc::parse_mdoc,
        runtime::algebra::RuntimeNat,
    };
    let fixture = &crate::mdoc::testcases::vectors::TEST_DATA;
    let mut zero_signature =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let f = crate::runtime::algebra::p256::P256Field::new();
    let q = crate::runtime::algebra::Q256Field::new();
    let curve = crate::runtime::algebra::secp256r1::Secp256r1::new(&f);
    zero_signature.issuer_sig_s = RuntimeNat::<4>::from_u64(0);
    assert!(super::push_witness_sig(&f, &q, &curve, &(f.one(), f.one()), &zero_signature).is_err());
}

#[test]
fn rejects_invalid_public_inputs_before_loading_or_sampling() {
    let spec = &crate::mdoc::runtime::tests_specs::v2_spec();
    let valid = req_attr("namespace", "a", [0xf5]);
    let now = "2026-10-23T00:00:00Z";
    let mut long_id = valid.clone();
    long_id.id = vec![b'a'; 31]; // CBOR header plus text exceeds the 32-byte slot.
    let mut long_value = valid.clone();
    long_value.cbor_value = crate::mdoc::circuits::cbor::encode_cbor_string(&[b'a'; 63]);
    let mut nested_value = valid.clone();
    nested_value.cbor_value = vec![0xc0; 100_000];
    nested_value.cbor_value.push(0x00);
    let long_doc = "x".repeat(33);
    let long_now = format!("{now}x");
    for (attrs, time, doc_type) in [
        (vec![], now, "doc"),
        (vec![valid.clone(), valid.clone()], now, "doc"),
        (vec![long_id], now, "doc"),
        (vec![long_value], now, "doc"),
        (vec![nested_value], now, "doc"),
        (vec![valid.clone()], &now[..19], "doc"),
        (vec![valid.clone()], long_now.as_str(), "doc"),
        (vec![valid.clone()], now, long_doc.as_str()),
    ] {
        let mut rng = DeterministicRng::new(42);
        // Deliberately invalid circuit and document bytes: validation must run first.
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                b"inputs",
                &attrs,
                time,
                doc_type,
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput)
        );
        assert_eq!(
            rng.state, 42,
            "invalid inputs must not consume prover randomness"
        );
        let expected = if attrs.len() == spec.num_attributes {
            MdocVerifierErrorCode::InvalidInput
        } else {
            MdocVerifierErrorCode::AttributeNumberMismatch
        };
        assert_eq!(
            run_mdoc_verifier(spec, &[], "0", "0", b"inputs", &attrs, time, doc_type, &[],),
            Err(expected)
        );
    }
    let boundary = req_attr(
        "namespace",
        [b'a'; 30],
        crate::mdoc::circuits::cbor::encode_cbor_string(&[b'a'; 62]),
    );
    assert!(super::public_inputs_fit(
        &[boundary],
        now.as_bytes(),
        &[b'x'; 32]
    ));
}

#[test]
fn private_hash_inputs_enforce_sha_capacity() {
    use crate::mdoc::{
        circuits::cbor::mdoc::parse_mdoc,
        proto::{
            hash::constants::K_MSO_PREIMAGE_LEN, mso_attribute::constants::K_MAX_ATTR_CBOR_LEN,
        },
    };
    let fixture = &crate::mdoc::testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3;
    let mut parsed = parse_mdoc::<crate::runtime::algebra::RuntimeNat<4>>(
        fixture.mdoc,
        fixture.transcript,
        "org.iso.18013.5.1.mDL",
    )
    .unwrap();
    let attribute = &parsed.attrs[0];
    let request = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    for length in [K_MAX_ATTR_CBOR_LEN, K_MAX_ATTR_CBOR_LEN + 1, 255, 256] {
        parsed.attrs[0].cbor_issuer_signed_item = vec![0; length];
        let result = super::push_witness_hash(&request, &parsed);
        if length == K_MAX_ATTR_CBOR_LEN {
            assert!(result.is_ok());
        } else {
            assert_eq!(result, Err(MdocProverErrorCode::AttributeTooLong));
        }
    }
    parsed.cbor_mso = vec![0; K_MSO_PREIMAGE_LEN];
    assert_eq!(
        super::push_witness_hash(&request, &parsed),
        Err(MdocProverErrorCode::TaggedMsoTooBig),
    );
}

#[test]
fn utc_public_input_syntax_is_checked_and_case_is_normalized() {
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let canonical = b"2026-10-23T00:00:00Z";
    for (position, byte) in [
        (4, b'/'),
        (7, b'/'),
        (10, b'X'),
        (13, b'-'),
        (16, b'-'),
        (19, b'X'),
        (0, b'x'),
        (18, b'x'),
    ] {
        let mut bad = *canonical;
        bad[position] = byte;
        assert!(!super::public_inputs_fit(&attrs, &bad, b"doc"));
    }
    assert!(!super::public_inputs_fit(&attrs, canonical, b""));
    let expected = super::timestamp_digits(canonical).unwrap();
    for (t, z) in [(b'T', b'Z'), (b'T', b'z'), (b't', b'Z'), (b't', b'z')] {
        let mut time = *canonical;
        time[10] = t;
        time[19] = z;
        assert!(super::public_inputs_fit(&attrs, &time, b"doc"));
        assert_eq!(super::timestamp_digits(&time).unwrap(), expected);
    }
}

#[test]
fn requested_values_must_match_before_building_sha_witnesses() {
    use crate::{mdoc::circuits::cbor::mdoc::parse_mdoc, runtime::algebra::RuntimeNat};
    let fixture = &crate::mdoc::testcases::vectors::TEST_DATA;
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let attr = &parsed.attrs[0];
    let mut value = attr.cbor_value.clone();
    value[0] ^= 1;
    let request = [req_attr("org.iso.18013.5.1", &attr.name, value)];
    assert_eq!(
        super::push_witness_hash(&request, &parsed),
        Err(MdocProverErrorCode::GeneralFailure)
    );
}
