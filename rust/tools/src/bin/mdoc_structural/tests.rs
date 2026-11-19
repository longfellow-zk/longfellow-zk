// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0

#[test]
fn public_cbor_hex_is_exact() {
    assert_eq!(super::decode_hex("0x190100").unwrap(), [0x19, 1, 0]);
    assert!(super::decode_hex("f").is_err());
    assert!(super::decode_hex("zz").is_err());
}

#[test]
fn request_slots_are_padded_and_disabled_fields_are_ignored() {
    let request = serde_json::json!({"attributes": [
        {"namespace":"ns", "id":"age_over_18", "value_cbor":"f5"},
        {"namespace":"ns", "enabled":false, "value_cbor":"invalid", "op":"unused"}
    ]});
    let attrs = super::requested_attributes(&request).unwrap();
    assert_eq!(attrs.len(), super::NEXT_ATTRIBUTES);
    assert!(attrs[0].enabled);
    assert_eq!(attrs[0].cbor_value, [0xf5]);
    for attr in &attrs[1..] {
        assert!(!attr.enabled);
        assert_eq!(attr.namespace_id, b"ns");
        assert!(attr.id.is_empty() && attr.cbor_value.is_empty());
    }
}

#[test]
fn date_slot_keeps_its_position_and_public_operator() {
    let request = serde_json::json!({"attributes": [
        {"namespace":"ns", "enabled":false},
        {"namespace":"ns", "enabled":false},
        {"namespace":"ns", "enabled":false},
        {"namespace":"ns", "id":"birth_date", "value_cbor":"d903ec6a313937312d30392d3031", "op":"le"}
    ]});
    let attrs = super::requested_attributes(&request).unwrap();
    assert!(attrs[..3].iter().all(|attr| !attr.enabled));
    assert!(attrs[3].enabled);
    assert_eq!(attrs[3].op, super::AttributeOp::Le);
}

#[test]
fn request_rejects_missing_disclosures_and_invalid_slot_flags() {
    for attributes in [
        serde_json::json!([]),
        serde_json::json!([{"namespace":"ns", "enabled":false}]),
        serde_json::json!([{"namespace":"ns", "enabled":"false"}]),
        serde_json::json!([{"namespace":"ns", "id":"x", "value_cbor":"00", "op":"lt"}]),
        serde_json::json!([{}, {}, {}, {}, {}]),
    ] {
        assert!(
            super::requested_attributes(&serde_json::json!({"attributes":attributes})).is_err()
        );
    }
}
