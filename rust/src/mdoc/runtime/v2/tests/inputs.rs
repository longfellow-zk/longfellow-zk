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
        runtime::tests::specs::{four_slots, v2_spec},
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
    let spec = v2_spec();
    let padded_attrs = four_slots(attrs.iter().cloned());
    let request = Request::check(
        &spec,
        fixture.pkx,
        fixture.pky,
        fixture.transcript,
        &padded_attrs,
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
    let attrs = four_slots([req_attr("namespace", "a", [0xf5])]);
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
        mso_attribute::constants::{K_DATE_MAX_ATTR_CBOR_LEN, K_DATE_SLOT, K_MAX_ATTR_CBOR_LEN},
    };
    let fixture = &BIRTHDATE_1971_09_01_MDOC_3;
    let mut parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, "org.iso.18013.5.1.mDL")
            .unwrap();
    let ns = "org.iso.18013.5.1";
    let ordinary = &parsed.attrs[0];
    let ordinary_request = req_attr(ns, &ordinary.name, &ordinary.cbor_value);
    let date_index = parsed
        .attrs
        .iter()
        .position(|attr| attr.name == b"birth_date")
        .unwrap();
    let date = &parsed.attrs[date_index];
    let mut date_request = four_slots([ordinary_request.clone()]);
    date_request[0].enabled = false;
    date_request[K_DATE_SLOT] = req_attr(ns, &date.name, &date.cbor_value);
    for (index, request, limit) in [
        (
            0,
            four_slots([ordinary_request.clone()]),
            K_MAX_ATTR_CBOR_LEN,
        ),
        (date_index, date_request, K_DATE_MAX_ATTR_CBOR_LEN),
    ] {
        for length in [119, 120, 183, 184, 247, 248, 255, 256] {
            let attr = &mut parsed.attrs[index];
            attr.cbor_issuer_signed_item = vec![0; length];
            // Patch the digest so that only slot capacity can fail during encoding.
            let digest = sha2::Sha256::digest(&attr.cbor_issuer_signed_item);
            let at = K_MSO_OFFSET + attr.mso_digest_offset_in_preimage + 2;
            parsed.cbor_mso[at..at + 32].copy_from_slice(&digest);
            let result = witness_hash(fixture, &request, &parsed);
            if length <= limit {
                assert!(
                    result.is_ok(),
                    "slot limit {limit}, item length {length}: {result:?}"
                );
            } else {
                assert_eq!(result, Err(MdocProverErrorCode::AttributeTooLong));
            }
        }
    }
    parsed.cbor_mso = vec![0; K_MSO_PREIMAGE_LEN];
    assert_eq!(
        witness_hash(fixture, &[ordinary_request], &parsed),
        Err(MdocProverErrorCode::TaggedMsoTooBig),
    );
}

#[test]
fn large_attribute_items_prove_and_verify_with_the_date_slot() {
    use sha2::{Digest, Sha256};

    use crate::{
        core::algebra::{ec::Curve, AlgebraicField, Nat, SupportsNatConversions},
        mdoc::{
            cbor::append_bytes_len,
            development_provider::tests::fixtures::next_circuit,
            proto::{
                hash::constants::{K_COSE1_PREFIX_LEN, K_MSO_OFFSET, K_TAG32},
                mso_attribute::constants::{K_ELEMENT_VALUE_PREFIX, K_MAX_ATTR_CBOR_LEN},
            },
            v2::{run_mdoc_prover_inner, run_mdoc_verifier},
        },
        runtime::random::DeterministicRng,
    };

    let fixture = &BIRTHDATE_1971_09_01_MDOC_3;
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let mut mdoc = fixture.mdoc.to_vec();
    let mut preimage = parsed.cbor_mso.clone();
    let find = |bytes: &[u8], target: &[u8]| {
        bytes
            .windows(target.len())
            .position(|window| window == target)
            .unwrap()
    };
    let ns = "org.iso.18013.5.1";
    let mut attrs = Vec::new();
    for (name, item_len) in [
        (b"family_name".as_slice(), 120),
        (b"height", 184),
        (b"age_over_18", K_MAX_ATTR_CBOR_LEN),
    ] {
        let attr = parsed.get_attribute(name).unwrap();
        let old = &attr.cbor_issuer_signed_item;
        let value_len = item_len - (old.len() - attr.cbor_value.len());
        let mut operand = Vec::new();
        append_bytes_len(&mut operand, value_len - 2);
        assert_eq!(operand.len(), 2);
        operand.resize(value_len, u8::try_from(attrs.len() + 1).unwrap());
        let value_slot = attr.field_locator.permutation >> 6;
        let value_start =
            attr.field_locator.slot_position[value_slot] + K_ELEMENT_VALUE_PREFIX.len();
        let value_end = value_start + attr.cbor_value.len();
        assert_eq!(&old[value_start..value_end], &attr.cbor_value);
        let mut item = old.clone();
        item.splice(value_start..value_end, operand.iter().copied());
        assert_eq!(item.len(), item_len);
        item[3] = u8::try_from(item.len() - 4).unwrap();
        let at = find(&mdoc, old);
        let digest_at = K_MSO_OFFSET + attr.mso_digest_offset_in_preimage;
        assert_eq!(&preimage[digest_at..digest_at + K_TAG32.len()], &K_TAG32);
        let digest_start = digest_at + K_TAG32.len();
        preimage[digest_start..digest_start + 32].copy_from_slice(&Sha256::digest(&item));
        mdoc.splice(at..at + old.len(), item);
        attrs.push(req_attr(ns, name, operand));
    }
    let date = parsed.get_attribute(b"birth_date").unwrap();
    attrs.push(req_attr(ns, &date.name, &date.cbor_value));

    // Replace the issuer signature with a test signature under d = k = 1.
    // The device signature still applies to the original session and device key.
    let wrapped_start = K_COSE1_PREFIX_LEN + 2;
    let old_wrapped = &parsed.cbor_mso[wrapped_start..];
    let at = find(&mdoc, old_wrapped);
    let sig = at + old_wrapped.len();
    mdoc[at..sig].copy_from_slice(&preimage[wrapped_start..]);
    assert_eq!(&mdoc[sig..sig + 2], b"\x58\x40");
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let (gx, gy) = curve.g();
    let r_scalar = f.to_nat(gx);
    let e = RuntimeNat::<4>::from_bytes_be(&Sha256::digest(&preimage));
    let s = q.to_nat(&q.addf(&q.reduce_nat(&e), &q.reduce_nat(&r_scalar)));
    let be = |nat: RuntimeNat<4>| nat.to_bytes_le().into_iter().rev().collect::<Vec<_>>();
    let r_bytes = be(r_scalar);
    mdoc[sig + 2..sig + 34].copy_from_slice(&r_bytes);
    mdoc[sig + 34..sig + 66].copy_from_slice(&be(s));
    let pkx = hex::encode(r_bytes);
    let pky = hex::encode(be(f.to_nat(gy)));

    let circuit = next_circuit();
    let proof = run_mdoc_prover_inner(
        circuit.spec(),
        circuit.compressed(),
        &mdoc,
        &pkx,
        &pky,
        fixture.transcript,
        &attrs,
        fixture.now,
        fixture.doc_type,
        &mut DeterministicRng::new(42),
    )
    .unwrap();
    run_mdoc_verifier(
        circuit.spec(),
        circuit.compressed(),
        &pkx,
        &pky,
        fixture.transcript,
        &attrs,
        fixture.now,
        fixture.doc_type,
        &proof,
    )
    .unwrap();
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

#[test]
fn disabled_hash_slots_ignore_payloads_and_artifact_width_is_exact() {
    use crate::mdoc::{
        cbor::structure_prover::ConcreteWitness as StructuralWitness,
        v2::{inputs::push_witness_hash_for_width, AttributeOp},
    };

    let fixture = &TEST_DATA;
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(fixture.mdoc, fixture.transcript, fixture.doc_type).unwrap();
    let fixture_attr = &parsed.attrs[0];
    let attrs = four_slots([req_attr(
        "org.iso.18013.5.1",
        &fixture_attr.name,
        &fixture_attr.cbor_value,
    )]);
    let mut ignored = attrs.clone();
    for attr in ignored.iter_mut().filter(|attr| !attr.enabled) {
        attr.id = b"not in the credential".to_vec();
        attr.cbor_value = vec![0xff; 300];
        attr.op = AttributeOp::Ge;
    }
    let spec = v2_spec();
    let field = P256Field::new();
    let checked = |slots| {
        Request::check(
            &spec,
            fixture.pkx,
            fixture.pky,
            fixture.transcript,
            slots,
            fixture.now,
            fixture.doc_type,
            &field,
        )
        .unwrap()
    };
    let request = checked(&attrs);
    let ignored_request = checked(&ignored);
    let base = witness_hash(fixture, &attrs, &parsed).unwrap();
    assert_eq!(witness_hash(fixture, &ignored, &parsed).unwrap(), base);
    assert_eq!(
        push_witness_hash_for_width(&request, &parsed, base.len()).unwrap(),
        base
    );

    let mut suffix_bits = 0;
    StructuralWitness::zero(attrs.len()).push(|_, bits| suffix_bits += bits);
    let structural_bits = base.len() + suffix_bits;
    let structural = push_witness_hash_for_width(&request, &parsed, structural_bits).unwrap();
    assert_eq!(structural.len(), structural_bits);
    assert_eq!(&structural[..base.len()], base);
    assert_eq!(
        push_witness_hash_for_width(&ignored_request, &parsed, structural_bits).unwrap(),
        structural
    );
    for invalid_width in [base.len() - 1, structural_bits + 1] {
        assert_eq!(
            push_witness_hash_for_width(&request, &parsed, invalid_width),
            Err(MdocProverErrorCode::WitnessCreationFailure)
        );
    }
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
    let attrs = four_slots([req_attr("namespace", "a", [0xf5])]);
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

#[test]
fn mso_capacity_is_checked_before_proving() {
    use crate::{
        mdoc::{
            cbor::{
                mdoc::{parse_mdoc, MdocParseError},
                test_utils::with_mso_size,
            },
            proto::hash::constants::K_MSO_MAX_BYTES,
            testcases::TEST_DATA,
        },
        runtime::algebra::RuntimeNat,
    };
    let (bytes, _) = with_mso_size(TEST_DATA.mdoc, K_MSO_MAX_BYTES).unwrap();
    let mut parsed =
        parse_mdoc::<RuntimeNat<4>>(&bytes, TEST_DATA.transcript, TEST_DATA.doc_type).unwrap();
    let attrs = [req_attr(
        "org.iso.18013.5.1",
        &parsed.attrs[0].name,
        &parsed.attrs[0].cbor_value,
    )];
    assert!(witness_hash(&TEST_DATA, &attrs, &parsed).is_ok());
    parsed.cbor_mso.push(0);
    assert_eq!(
        witness_hash(&TEST_DATA, &attrs, &parsed),
        Err(MdocProverErrorCode::TaggedMsoTooBig)
    );
    let (oversized, _) = with_mso_size(TEST_DATA.mdoc, K_MSO_MAX_BYTES + 1).unwrap();
    assert!(matches!(
        parse_mdoc::<RuntimeNat<4>>(&oversized, TEST_DATA.transcript, TEST_DATA.doc_type),
        Err(MdocParseError::TooBig)
    ));
}
