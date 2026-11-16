// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::algebra::encoding::P256_MODULUS,
    mdoc::{
        cbor::mdoc::parse_mdoc,
        proto::hash::constants::K_MSO_OFFSET,
        runtime::tests::specs::v2_spec,
        testcases::TEST_DATA,
        v2::{document::*, req_attr},
    },
};

fn map() -> CborElement {
    let parsed =
        parse_mdoc::<RuntimeNat<4>>(TEST_DATA.mdoc, TEST_DATA.transcript, TEST_DATA.doc_type)
            .unwrap();
    let start = K_MSO_OFFSET;
    crate::mdoc::cbor::parse::CborParser::new(&parsed.cbor_mso[start..])
        .parse_exact()
        .unwrap()
}
fn entry_mut<'a>(map: &'a mut CborElement, name: &str) -> &'a mut CborElement {
    let CborValue::Map(entries) = &mut map.value else {
        panic!("map");
    };
    &mut entries
        .iter_mut()
        .find(|(k, _)| matches!(&k.value,CborValue::Text(s) if s == name))
        .unwrap()
        .1
}
fn key_mut(map: &mut CborElement, index: i128) -> &mut CborElement {
    let key = entry_mut(entry_mut(map, "deviceKeyInfo"), "deviceKey");
    let CborValue::Map(entries) = &mut key.value else {
        panic!("key map");
    };
    &mut entries
        .iter_mut()
        .find(|(k, _)| matches!(k.value,CborValue::Integer(n) if n == index))
        .unwrap()
        .1
}
#[test]
fn v2_document_validates_original_device_key_before_integer_conversion() {
    let field = P256Field::new();
    let spec = v2_spec();
    let attrs = [req_attr("org.iso.18013.5.1", "a", [0xf5])];
    let request = Request::check(
        &spec,
        TEST_DATA.pkx,
        TEST_DATA.pky,
        TEST_DATA.transcript,
        &attrs,
        TEST_DATA.now,
        TEST_DATA.doc_type,
        &field,
    )
    .unwrap();
    parse(TEST_DATA.mdoc, &request, &field).unwrap();
    let mut noncanonical = P256_MODULUS.to_vec();
    noncanonical.reverse();
    for (index, value) in [
        (1, CborValue::Integer(1)),
        (-1, CborValue::Integer(2)),
        (-2, CborValue::Bytes(vec![0; 31])),
        (-2, CborValue::Bytes(vec![0; 33])),
        (-3, CborValue::Bytes(vec![0; 33])),
        (-2, CborValue::Bytes(noncanonical)),
        (-2, CborValue::Bytes(vec![0; 32])),
    ] {
        let mut changed = map();
        key_mut(&mut changed, index).value = value;
        assert!(validate_mso(&changed, TEST_DATA.doc_type, TEST_DATA.now, &field).is_err());
    }
    let mut duplicate = map();
    let CborValue::Map(entries) =
        &mut entry_mut(entry_mut(&mut duplicate, "deviceKeyInfo"), "deviceKey").value
    else {
        panic!("key map");
    };
    entries.push(entries[0].clone());
    assert!(validate_mso(&duplicate, TEST_DATA.doc_type, TEST_DATA.now, &field).is_err());
}
#[test]
fn v2_document_checks_signed_doc_type_and_validity_before_proving() {
    let field = P256Field::new();
    let mso = map();
    assert!(validate_mso(&mso, "wrong", TEST_DATA.now, &field).is_err());
    for now in [
        "0000-01-01T00:00:00Z",
        "9999-12-31T23:59:59Z",
        "2026-01-01X00:00:00Z",
    ] {
        assert!(validate_mso(&mso, TEST_DATA.doc_type, now, &field).is_err());
    }
    let validity = text_entry(&mso, "validityInfo", "test").unwrap();
    for name in ["validFrom", "validUntil"] {
        let element = text_entry(validity, name, "test").unwrap();
        let CborValue::Tag(0, inner) = &element.value else {
            panic!("timestamp tag");
        };
        let CborValue::Text(now) = &inner.value else {
            panic!("timestamp text");
        };
        validate_mso(&mso, TEST_DATA.doc_type, now, &field).unwrap();
        let mut changed = mso.clone();
        let field_value = entry_mut(entry_mut(&mut changed, "validityInfo"), name);
        field_value.value = CborValue::Tag(
            0,
            Box::new(CborElement {
                value: CborValue::Text("2026-01-01X00:00:00Z".into()),
                start: 0,
                end: 20,
            }),
        );
        assert!(validate_mso(&changed, TEST_DATA.doc_type, TEST_DATA.now, &field).is_err());
    }
}

#[test]
fn v2_document_preserves_structural_errors_and_predicate_failures() {
    let field = P256Field::new();
    for name in ["docType", "validityInfo", "deviceKeyInfo"] {
        let mut mso = map();
        let CborValue::Map(entries) = &mut mso.value else {
            panic!("map")
        };
        entries.retain(|(key, _)| !matches!(&key.value, CborValue::Text(text) if text == name));
        assert!(matches!(
            validate_mso(&mso, TEST_DATA.doc_type, TEST_DATA.now, &field),
            Err(Error::Encoding(MdocParseError::MissingField(_)))
        ));
    }
    let mut wrong_type = map();
    entry_mut(&mut wrong_type, "docType").value = CborValue::Integer(0);
    assert!(matches!(
        validate_mso(&wrong_type, TEST_DATA.doc_type, TEST_DATA.now, &field),
        Err(Error::Encoding(MdocParseError::UnexpectedType(
            "MSO.docType"
        )))
    ));
    assert!(matches!(
        validate_mso(&map(), "wrong", TEST_DATA.now, &field),
        Err(Error::Predicate)
    ));
    assert!(matches!(
        validate_mso(&map(), TEST_DATA.doc_type, "9999-12-31T23:59:59Z", &field),
        Err(Error::Predicate)
    ));
}

#[test]
fn v2_document_requires_the_circuit_timestamp_headers() {
    use crate::mdoc::cbor::parse::CborParser;
    for (prefix, accepted) in [
        (&[0xc0, 0x74][..], true),
        (&[0xc0, 0x78, 20][..], false),
        (&[0xd8, 0, 0x74][..], false),
    ] {
        let mut encoded = prefix.to_vec();
        encoded.extend_from_slice(b"2026-01-01T00:00:00Z");
        let parsed = CborParser::new(&encoded).parse_exact().unwrap();
        assert_eq!(timestamp(&parsed).is_ok(), accepted);
    }
}

#[test]
fn v2_document_requires_the_circuit_device_key_layout() {
    let field = P256Field::new();
    let check = |mso: &CborElement| validate_mso(mso, TEST_DATA.doc_type, TEST_DATA.now, &field);
    check(&map()).unwrap();
    for swap in [true, false] {
        let mut mso = map();
        let CborValue::Map(entries) =
            &mut entry_mut(entry_mut(&mut mso, "deviceKeyInfo"), "deviceKey").value
        else {
            panic!("key map")
        };
        if swap {
            entries.swap(0, 1);
        } else {
            entries.push(entries[0].clone());
        }
        assert!(matches!(
            check(&mso),
            Err(Error::Encoding(MdocParseError::UnsupportedEncoding))
        ));
    }
    let mut extra_info = map();
    let CborValue::Map(entries) = &mut entry_mut(&mut extra_info, "deviceKeyInfo").value else {
        panic!("info map")
    };
    entries.push(entries[0].clone());
    assert!(check(&extra_info).is_err());
    let mut nonminimal = map();
    key_mut(&mut nonminimal, -2).end += 1;
    assert!(matches!(
        check(&nonminimal),
        Err(Error::Encoding(MdocParseError::UnsupportedEncoding))
    ));
    let mut nonminimal = map();
    let CborValue::Map(entries) = &mut nonminimal.value else {
        panic!("map")
    };
    entries
        .iter_mut()
        .find(|(k, _)| matches!(&k.value, CborValue::Text(s) if s == "deviceKeyInfo"))
        .unwrap()
        .0
        .end += 1;
    assert!(matches!(
        check(&nonminimal),
        Err(Error::Encoding(MdocParseError::UnsupportedEncoding))
    ));
}

#[test]
fn documents_longer_than_the_cap_are_rejected_before_parsing() {
    let field = P256Field::new();
    let spec = v2_spec();
    let attrs = [req_attr("org.iso.18013.5.1", "a", [0xf5])];
    let request = Request::check(
        &spec,
        TEST_DATA.pkx,
        TEST_DATA.pky,
        TEST_DATA.transcript,
        &attrs,
        TEST_DATA.now,
        TEST_DATA.doc_type,
        &field,
    )
    .unwrap();
    // The fixture followed by zeros: at the cap it is parsed (and rejected for
    // its trailing bytes); one byte more and it is rejected unparsed.
    let mut padded = TEST_DATA.mdoc.to_vec();
    padded.resize(MAX_DOCUMENT_BYTES, 0);
    assert!(matches!(
        parse(&padded, &request, &field),
        Err(Error::Encoding(_))
    ));
    padded.push(0);
    assert!(matches!(
        parse(&padded, &request, &field),
        Err(Error::TooLong)
    ));
}
