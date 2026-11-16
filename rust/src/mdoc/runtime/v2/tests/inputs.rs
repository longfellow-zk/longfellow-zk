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

//! V2 private witness encoding.
use crate::{
    mdoc::{
        cbor::mdoc::{parse_mdoc, ParsedMdoc},
        runtime::tests::specs::v2_spec,
        testcases::{
            TestDataStatic, BIRTHDATE_1971_09_01_MDOC_3, DHS_COMPLIANCE_MDOC_10, TEST_DATA,
        },
        v2::{req_attr, request::Request, MdocProverErrorCode, RequestedAttribute},
    },
    runtime::algebra::{
        p256::{P256Element, P256Field},
        q256::Q256Field,
        secp256r1::Secp256r1,
        RuntimeNat,
    },
};

/// The hash witness for `attrs`, checked as a request with the fixture's
/// issuer key, session transcript, time and document type.
fn witness_hash(
    fixture: &TestDataStatic,
    attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<RuntimeNat<4>>,
) -> Result<Vec<bool>, MdocProverErrorCode> {
    let mut spec = v2_spec();
    spec.num_attributes = attrs.len();
    let request = Request::check(
        &spec,
        fixture.pkx,
        fixture.pky,
        fixture.transcript,
        attrs,
        fixture.now,
        fixture.doc_type,
        &P256Field::new(),
    )
    .expect("the test request passes the request check");
    super::super::inputs::push_witness_hash(&request, parsed)
}

#[test]
fn global_namespace_scopes_the_honest_attribute_lookup() {
    let fixture = &DHS_COMPLIANCE_MDOC_10;
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
    let expected = witness_hash(fixture, &request, &parsed).unwrap();
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
        witness_hash(fixture, &request, &with_duplicate).unwrap(),
        expected,
        "a matching name in a different namespace must not shadow the selected attribute"
    );
    let wrong = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    assert_eq!(
        witness_hash(fixture, &wrong, &parsed),
        Err(MdocProverErrorCode::AttributeNotFound)
    );
}

#[test]
fn zero_signature_is_a_witness_error() {
    use crate::core::algebra::{AlgebraicField, Nat};
    let fixture = &TEST_DATA;
    let mut zero_signature =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    zero_signature.issuer_sig_s = RuntimeNat::<4>::from_u64(0);
    let spec = v2_spec();
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let request = Request::check(
        &spec,
        "1",
        "1",
        fixture.transcript,
        &attrs,
        fixture.now,
        fixture.doc_type,
        &f,
    )
    .unwrap();
    assert_eq!(request.issuer_pk(), &(f.one(), f.one()));
    assert_eq!(
        super::super::inputs::push_witness_sig(&f, &q, &curve, &request, &zero_signature),
        Err(MdocProverErrorCode::WitnessCreationFailure)
    );
}

#[test]
fn private_hash_inputs_enforce_sha_capacity() {
    use sha2::Digest;

    use crate::mdoc::proto::{
        hash::constants::{K_MSO_OFFSET, K_MSO_PREIMAGE_LEN},
        mso_attribute::constants::K_MAX_ATTR_CBOR_LEN,
    };
    let fixture = &BIRTHDATE_1971_09_01_MDOC_3;
    let mut parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, "org.iso.18013.5.1.mDL")
            .unwrap();
    let attribute = &parsed.attrs[0];
    let request = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    for length in [K_MAX_ATTR_CBOR_LEN, K_MAX_ATTR_CBOR_LEN + 1, 255, 256] {
        parsed.attrs[0].cbor_issuer_signed_item = vec![0; length];
        // Sign the replaced item into the MSO, so that only its length can fail.
        let digest = sha2::Sha256::digest(&parsed.attrs[0].cbor_issuer_signed_item);
        let at = K_MSO_OFFSET + parsed.attrs[0].mso_digest_offset_in_preimage + 2;
        parsed.cbor_mso[at..at + 32].copy_from_slice(&digest);
        let result = witness_hash(fixture, &request, &parsed);
        if length == K_MAX_ATTR_CBOR_LEN {
            assert!(result.is_ok());
        } else {
            assert_eq!(result, Err(MdocProverErrorCode::AttributeTooLong));
        }
    }
    parsed.cbor_mso = vec![0; K_MSO_PREIMAGE_LEN];
    assert_eq!(
        witness_hash(fixture, &request, &parsed),
        Err(MdocProverErrorCode::TaggedMsoTooBig),
    );
}

#[test]
fn requested_values_must_match_before_building_sha_witnesses() {
    let fixture = &TEST_DATA;
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let attr = &parsed.attrs[0];
    let mut value = attr.cbor_value.clone();
    value[0] ^= 1;
    let request = [req_attr("org.iso.18013.5.1", &attr.name, value)];
    assert_eq!(
        witness_hash(fixture, &request, &parsed),
        Err(MdocProverErrorCode::GeneralFailure)
    );
}

/// The signature witness for the fixture's document, checked as a request
/// with the issuer key `(pkx, pky)` and the session transcript `transcript`.
fn witness_sig(
    fixture: &TestDataStatic,
    pkx: &str,
    pky: &str,
    transcript: &[u8],
) -> Result<Vec<P256Element>, MdocProverErrorCode> {
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let parsed = parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, transcript, fixture.doc_type).unwrap();
    let spec = v2_spec();
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let request = Request::check(
        &spec,
        pkx,
        pky,
        transcript,
        &attrs,
        fixture.now,
        fixture.doc_type,
        &f,
    )
    .unwrap();
    super::super::inputs::push_witness_sig(&f, &q, &curve, &request, &parsed)
}

#[test]
fn signatures_the_circuit_rejects_fail_while_encoding() {
    let fixture = &TEST_DATA;
    assert!(witness_sig(fixture, fixture.pkx, fixture.pky, fixture.transcript).is_ok());
    // Another key on the curve: the generator. The issuer signature fails.
    let (gx, gy) = (
        "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
    );
    assert_eq!(
        witness_sig(fixture, gx, gy, fixture.transcript),
        Err(MdocProverErrorCode::GeneralFailure)
    );
    // A key off the curve.
    assert_eq!(
        witness_sig(fixture, fixture.pkx, "1", fixture.transcript),
        Err(MdocProverErrorCode::GeneralFailure)
    );
    // Another session: the device signature fails.
    assert_eq!(
        witness_sig(fixture, fixture.pkx, fixture.pky, b"\x66inputs"),
        Err(MdocProverErrorCode::GeneralFailure)
    );
}

#[test]
fn attribute_items_the_issuer_did_not_sign_fail_while_encoding() {
    let fixture = &TEST_DATA;
    let mut parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let attribute = &parsed.attrs[0];
    let request = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    assert!(witness_hash(fixture, &request, &parsed).is_ok());
    // A byte of the item's `random` field: the item no longer matches its
    // digest in the MSO.
    let item = &mut parsed.attrs[0].cbor_issuer_signed_item;
    let last = item.len() - 1;
    item[last] ^= 1;
    assert_eq!(
        witness_hash(fixture, &request, &parsed),
        Err(MdocProverErrorCode::GeneralFailure)
    );
}
