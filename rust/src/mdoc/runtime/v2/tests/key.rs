// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{core::algebra::AlgebraicField, mdoc::v2::key::*, runtime::algebra::p256::P256Field};

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

/// The accepted spellings of one value: with or without `0x`, any case, any
/// number of leading zeros up to 64 digits. The digits are big-endian and
/// the largest canonical value, the modulus minus one, is accepted.
#[test]
fn coordinates_accept_every_spelling_of_a_value() {
    let p = P256Field::new();
    let parse = |text: &str| parse_pk_coordinate(text, &p).unwrap();
    let two_five_six = (0..8).fold(p.one(), |x, _| p.addf(&x, &x));
    for text in ["100", "0x100", "0x0100", &format!("{:0>64}", "100")] {
        assert_eq!(parse(text), two_five_six, "{text:?}");
    }
    assert_eq!(parse("0xABCDEF"), parse("abcdef"));
    assert_eq!(parse("0xAbCdEf"), parse("0x00abcdef"));
    assert_eq!(
        parse("ffffffff00000001000000000000000000000000fffffffffffffffffffffffe"),
        p.mone()
    );
    for text in ["0x0x1", "0X1", " 1", "1 ", &format!("0x{}", "0".repeat(65))] {
        assert!(parse_pk_coordinate(text, &p).is_err(), "{text:?}");
    }
}
