// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::mdoc::circuits::cbor::{append_bytes_len, append_text_len};

#[test]
fn byte_string_length_boundaries() {
    let cases: &[(usize, &[u8])] = &[
        (23, &[0x57]),
        (24, &[0x58, 0x18]),
        (255, &[0x58, 0xff]),
        (256, &[0x59, 0x01, 0x00]),
        (65_535, &[0x59, 0xff, 0xff]),
        (65_536, &[0x5a, 0x00, 0x01, 0x00, 0x00]),
        (u32::MAX as usize, &[0x5a, 0xff, 0xff, 0xff, 0xff]),
    ];

    for &(len, expected) in cases {
        let mut encoded = Vec::new();
        append_bytes_len(&mut encoded, len);
        assert_eq!(encoded, expected, "incorrect encoding for length {len}");
    }
}

#[test]
fn text_string_length_boundaries() {
    let cases: &[(usize, &[u8])] = &[
        (23, &[0x77]),
        (24, &[0x78, 0x18]),
        (255, &[0x78, 0xff]),
        (256, &[0x79, 0x01, 0x00]),
        (65_535, &[0x79, 0xff, 0xff]),
        (65_536, &[0x7a, 0x00, 0x01, 0x00, 0x00]),
        (u32::MAX as usize, &[0x7a, 0xff, 0xff, 0xff, 0xff]),
    ];

    for &(len, expected) in cases {
        let mut encoded = Vec::new();
        append_text_len(&mut encoded, len);
        assert_eq!(encoded, expected, "incorrect encoding for length {len}");
    }
}

#[cfg(target_pointer_width = "64")]
#[test]
fn string_length_above_u32() {
    let len = u32::MAX as usize + 1;

    let mut bytes = Vec::new();
    append_bytes_len(&mut bytes, len);
    assert_eq!(bytes, [0x5b, 0, 0, 0, 1, 0, 0, 0, 0]);

    let mut text = Vec::new();
    append_text_len(&mut text, len);
    assert_eq!(text, [0x7b, 0, 0, 0, 1, 0, 0, 0, 0]);
}
