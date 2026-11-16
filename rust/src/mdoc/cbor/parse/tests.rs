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

use super::{CborParser, CborValue};

#[test]
fn bounded_nesting_for_tags_arrays_and_maps() {
    for prefix in [&[0xc0][..], &[0x81][..], &[0xa1, 0x00][..]] {
        for depth in [super::MAX_DEPTH, super::MAX_DEPTH + 1, 100_000] {
            let mut bytes = prefix.repeat(depth);
            bytes.push(0x00);
            let result = CborParser::new(&bytes).parse_exact();
            if depth <= super::MAX_DEPTH {
                assert!(result.is_ok());
            } else {
                assert_eq!(result.unwrap_err(), "CBOR nesting limit exceeded");
            }
        }
    }
}

fn parse_integer(data: &[u8]) -> i128 {
    let mut parser = CborParser::new(data);
    let element = parser.parse_exact().expect("test CBOR must be valid");
    let CborValue::Integer(value) = element.value else {
        panic!("test CBOR must be an integer");
    };
    value
}

#[test]
fn parses_positive_and_negative_integers_semantically() {
    assert_eq!(parse_integer(&[0x00]), 0);
    assert_eq!(
        parse_integer(&[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
        u64::MAX.into()
    );
    assert_eq!(parse_integer(&[0x20]), -1);
    assert_eq!(parse_integer(&[0x21]), -2);
    assert_eq!(
        parse_integer(&[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
        -18_446_744_073_709_551_616
    );
}

#[test]
fn parses_extended_simple_values() {
    let mut parser = CborParser::new(&[0xf8, 0x20]);
    let element = parser.parse_exact().expect("test CBOR must be valid");
    assert!(matches!(element.value, CborValue::Simple(32)));
}

#[test]
fn preserves_floating_point_bits() {
    let mut half_parser = CborParser::new(&[0xf9, 0x3c, 0x00]);
    let half = half_parser
        .parse_exact()
        .expect("half-float CBOR must be valid");
    assert!(matches!(half.value, CborValue::Float16(0x3c00)));

    let mut single_parser = CborParser::new(&[0xfa, 0x3f, 0x80, 0x00, 0x00]);
    let single = single_parser
        .parse_exact()
        .expect("single-float CBOR must be valid");
    assert!(matches!(single.value, CborValue::Float32(0x3f80_0000)));

    let mut double_parser =
        CborParser::new(&[0xfb, 0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    let double = double_parser
        .parse_exact()
        .expect("double-float CBOR must be valid");
    assert!(matches!(
        double.value,
        CborValue::Float64(0x3ff0_0000_0000_0000)
    ));
}

#[test]
fn rejects_trailing_data_without_parsing_it() {
    let mut parser = CborParser::new(&[0x01, 0xff]);
    assert_eq!(
        parser
            .parse_exact()
            .expect_err("trailing data must be rejected"),
        "Trailing data after CBOR item: 1 bytes"
    );
}
