// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::{Digest, Sha256};

use super::{
    compute_transcript_hash, parse_mdoc, parse_signature, required_map_value, validate_mso_layout,
    MdocParseError,
};
use crate::{
    compile::algebra::CompileNat,
    mdoc::circuits::cbor::{
        constants::{K_COSE_SIGN1_SIGNING_HEADER, K_DEVICE_AUTHENTICATION_HEADER},
        parse::CborParser,
    },
};

fn wrapped_mso(map_len: usize) -> (Vec<u8>, Vec<u8>) {
    let map = vec![0; map_len];
    let mut wrapped = vec![0xd8, 0x18, 0x59];
    wrapped.extend_from_slice(&(map_len as u16).to_be_bytes());
    wrapped.extend_from_slice(&map);
    (wrapped, map)
}

#[test]
fn validates_fixed_mso_layout() {
    let (valid_wrapped, valid_map) = wrapped_mso(256);
    assert_eq!(validate_mso_layout(&valid_wrapped, &valid_map), Ok(()));

    let (short_wrapped, short_map) = wrapped_mso(255);
    assert_eq!(
        validate_mso_layout(&short_wrapped, &short_map),
        Err(MdocParseError::UnsupportedEncoding)
    );

    let (mut wrong_len_wrapped, wrong_len_map) = wrapped_mso(256);
    wrong_len_wrapped[4] = 1;
    assert_eq!(
        validate_mso_layout(&wrong_len_wrapped, &wrong_len_map),
        Err(MdocParseError::UnsupportedEncoding)
    );

    let (mut trailing_wrapped, trailing_map) = wrapped_mso(256);
    trailing_wrapped.push(0);
    assert_eq!(
        validate_mso_layout(&trailing_wrapped, &trailing_map),
        Err(MdocParseError::UnsupportedEncoding)
    );
}

#[test]
fn rejects_mso_that_exceeds_sha_capacity() {
    let (wrapped, map) = wrapped_mso(2527);
    assert_eq!(
        validate_mso_layout(&wrapped, &map),
        Err(MdocParseError::TooBig)
    );
}

#[test]
fn malformed_mdoc_returns_an_error() {
    assert!(matches!(
        parse_mdoc::<CompileNat<4>>(&[], &[], ""),
        Err(MdocParseError::Cbor {
            context: "root mdoc",
            ..
        })
    ));
}

#[test]
fn nested_decoy_key_does_not_satisfy_schema() {
    let encoded = [
        0xa1, 0x65, b'o', b'u', b't', b'e', b'r', 0xa1, 0x69, b'd', b'o', b'c', b'u', b'm', b'e',
        b'n', b't', b's', 0x80,
    ];
    let mut parser = CborParser::new(&encoded);
    let root = parser.parse_exact().expect("test CBOR must be valid");

    assert!(matches!(
        required_map_value(&root, "documents", "root.documents"),
        Err(MdocParseError::MissingField("root.documents"))
    ));
}

#[test]
fn duplicate_schema_key_is_rejected() {
    let encoded = [
        0xa2, 0x69, b'd', b'o', b'c', b'u', b'm', b'e', b'n', b't', b's', 0x80, 0x69, b'd', b'o',
        b'c', b'u', b'm', b'e', b'n', b't', b's', 0x80,
    ];
    let mut parser = CborParser::new(&encoded);
    let root = parser.parse_exact().expect("test CBOR must be valid");

    assert!(matches!(
        required_map_value(&root, "documents", "root.documents"),
        Err(MdocParseError::DuplicateField("root.documents"))
    ));
}

#[test]
fn wrong_schema_container_type_is_rejected() {
    let encoded = [
        0xa1, 0x69, b'd', b'o', b'c', b'u', b'm', b'e', b'n', b't', b's', 0x00,
    ];
    assert!(matches!(
        parse_mdoc::<CompileNat<4>>(&encoded, &[], ""),
        Err(MdocParseError::UnexpectedType("root.documents"))
    ));
}

#[test]
fn trailing_cbor_data_is_rejected() {
    assert!(matches!(
        parse_mdoc::<CompileNat<4>>(&[0xa0, 0x00], &[], ""),
        Err(MdocParseError::Cbor {
            context: "root mdoc",
            message,
        }) if message.starts_with("Trailing data after CBOR item")
    ));
}

#[test]
fn malformed_signature_returns_an_error() {
    assert_eq!(
        parse_signature::<CompileNat<4>>(&[0; 63], "issuer signature"),
        Err(MdocParseError::InvalidLength {
            field: "issuer signature",
            expected: 64,
            actual: 63,
        })
    );
}

#[test]
fn transcript_hash_uses_u32_lengths() {
    // An empty docType gives a fixed 27-byte overhead in DeviceAuthentication.
    let transcript = vec![0; 65_536 - 27];
    let actual = compute_transcript_hash(&transcript, "");

    let mut device_authentication = K_DEVICE_AUTHENTICATION_HEADER.to_vec();
    device_authentication.extend_from_slice(&transcript);
    device_authentication.push(0x60);
    device_authentication.extend_from_slice(&[0xd8, 0x18, 0x41, 0xa0]);
    assert_eq!(device_authentication.len(), 65_536);

    let mut expected_preimage = K_COSE_SIGN1_SIGNING_HEADER.to_vec();
    expected_preimage.extend_from_slice(&[0x5a, 0x00, 0x01, 0x00, 0x07]);
    expected_preimage.extend_from_slice(&[0xd8, 0x18, 0x5a, 0x00, 0x01, 0x00, 0x00]);
    expected_preimage.extend_from_slice(&device_authentication);
    let expected = Sha256::digest(&expected_preimage).to_vec();

    assert_eq!(actual, expected);
}
fn item_payload(digest: &[u8], random: &[u8]) -> Vec<u8> {
    let mut payload = b"\xa4\x68digestID".to_vec();
    payload.extend_from_slice(digest);
    payload.extend_from_slice(b"\x66random");
    payload.extend_from_slice(random);
    payload.extend_from_slice(b"\x71elementIdentifier\x64name\x6celementValue\xf5");
    payload
}

fn item_witness(payload: &[u8], wide_header: bool) -> Result<super::ParsedAttr, MdocParseError> {
    let mut wrapped = vec![0xd8, 0x18];
    if wide_header {
        wrapped.extend_from_slice(&[0x59, 0]);
    } else {
        wrapped.push(0x58);
    }
    wrapped.push(payload.len() as u8);
    wrapped.extend_from_slice(payload);
    let inner = CborParser::new(payload).parse_exact().unwrap();
    let mut digests = b"\xa1\x62ns\xa1\x01\x58\x20".to_vec();
    digests.extend_from_slice(&[0; 32]);
    let digests = CborParser::new(&digests).parse_exact().unwrap();
    super::compute_witness(
        b"name".to_vec(),
        vec![0xf5],
        &wrapped,
        &inner,
        &digests,
        "ns",
    )
}

#[test]
fn item_witness_rejects_encodings_outside_the_circuit_layout() {
    for digest in [&[1][..], &[0x1a, 0, 0, 0, 1][..]] {
        let payload = item_payload(digest, &[0x41, 7]);
        let witness = item_witness(&payload, false).unwrap();
        assert_eq!(witness.field_locator.slot_position[0], 5);
        assert!(matches!(
            item_witness(&payload, true),
            Err(MdocParseError::UnsupportedEncoding)
        ));
    }
    let wide_id = item_payload(&[0x1b, 0, 0, 0, 0, 0, 0, 0, 1], &[0x41, 7]);
    assert!(matches!(
        item_witness(&wide_id, false),
        Err(MdocParseError::UnsupportedEncoding)
    ));
    for random in [&[0x61, b'r'][..], &[0][..]] {
        assert!(matches!(
            item_witness(&item_payload(&[1], random), false),
            Err(MdocParseError::UnexpectedType("IssuerSignedItem.random"))
        ));
    }
    assert!(item_witness(&item_payload(&[1], &[0x58, 1, 7]), false).is_ok());
    assert!(matches!(
        item_witness(&item_payload(&[1], &[0x59, 0, 1, 7]), false),
        Err(MdocParseError::UnsupportedEncoding)
    ));
    let mut wide_map = item_payload(&[1], &[0x41, 7]);
    wide_map.splice(0..1, [0xb8, 4]);
    assert!(matches!(
        item_witness(&wide_map, false),
        Err(MdocParseError::UnsupportedEncoding)
    ));
    let mut wide_key = item_payload(&[1], &[0x41, 7]);
    wide_key.splice(1..2, [0x78, 8]);
    assert!(matches!(
        item_witness(&wide_key, false),
        Err(MdocParseError::UnsupportedEncoding)
    ));
}

#[test]
fn element_identifiers_are_unique_only_within_their_namespace() {
    let payload = item_payload(&[1], &[0x41, 7]);
    let mut item = vec![0xd8, 0x18, 0x58, payload.len() as u8];
    item.extend_from_slice(&payload);
    let mut digests = b"\xa2\x62ns\xa1\x01\x58\x20".to_vec();
    digests.extend_from_slice(&[0; 32]);
    digests.extend_from_slice(b"\x62ot\xa1\x01\x58\x20");
    digests.extend_from_slice(&[0; 32]);
    let digests = CborParser::new(&digests).parse_exact().unwrap();
    for same_namespace in [true, false] {
        let mut encoded = b"\xa1\x6anameSpaces".to_vec();
        encoded.extend_from_slice(if same_namespace {
            b"\xa1\x62ns\x82"
        } else {
            b"\xa2\x62ns\x81"
        });
        encoded.extend_from_slice(&item);
        if !same_namespace {
            encoded.extend_from_slice(b"\x62ot\x81");
        }
        encoded.extend_from_slice(&item);
        let issuer = CborParser::new(&encoded).parse_exact().unwrap();
        let result = super::extract_attrs(&issuer, &encoded, &digests);
        if same_namespace {
            assert!(matches!(
                result,
                Err(MdocParseError::DuplicateField(
                    "namespace elementIdentifier"
                ))
            ));
        } else {
            let attributes = result.unwrap();
            assert_eq!(attributes.len(), 2);
            assert_eq!(attributes[0].name, attributes[1].name);
        }
    }
}
