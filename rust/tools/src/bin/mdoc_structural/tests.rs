// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0

#[test]
fn public_cbor_hex_is_exact() {
    assert_eq!(super::decode_hex("0x190100").unwrap(), [0x19, 1, 0]);
    assert!(super::decode_hex("f").is_err());
    assert!(super::decode_hex("zz").is_err());
}
