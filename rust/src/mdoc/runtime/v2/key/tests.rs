// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core::algebra::AlgebraicField;

#[test]
fn coordinates_require_a_nonempty_canonical_field_value() {
    let p = P256Field::new();
    for text in ["", "0x", "-1", "0xgg", "é"] {
        assert!(parse_pk_coordinate(text, &p).is_err(), "{text:?}");
    }
    assert_eq!(parse_pk_coordinate("0", &p).unwrap(), p.zero());
    assert_eq!(parse_pk_coordinate("0x01", &p).unwrap(), p.one());
    assert_eq!(
        parse_pk_coordinate(&format!("{:0>64}", "1"), &p).unwrap(),
        p.one()
    );
    assert!(parse_pk_coordinate(&"f".repeat(65), &p).is_err());
    assert!(parse_pk_coordinate(
        "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        &p
    )
    .is_err());
}
