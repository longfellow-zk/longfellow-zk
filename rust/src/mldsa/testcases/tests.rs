// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::decode_hex;

#[test]
fn fixture_hex_accepts_both_cases() {
    assert_eq!(decode_hex("00aAfF"), [0, 170, 255]);
}

#[test]
#[should_panic(expected = "fixture hex must contain whole bytes")]
fn fixture_hex_rejects_partial_bytes() {
    let _ = decode_hex("abc");
}
