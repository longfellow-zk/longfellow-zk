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

use super::{push_input_hash, push_input_sig, HashInputError};
use crate::{
    core::algebra::{AlgebraicField, Nat, SupportsNatConversions},
    mdoc::v1::attribute::req_attr,
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field, RuntimeNat},
};

#[test]
fn push_input_sig_reduces_e2_at_or_above_p() {
    let p256 = P256Field::new();
    let pk = (p256.one(), p256.one());
    let macs = [0u128; 6];
    let av = 0u128;

    // 2^256 - 1 >= p (P-256 base prime); must reduce mod p instead of panicking.
    let e2_max = RuntimeNat::<4>::from_bytes_be(&[0xffu8; 32]);
    let inputs = push_input_sig(&p256, &pk, &e2_max, &macs, av);
    assert_eq!(inputs[3], p256.reduce_nat(&e2_max));

    // Exact P-256 base prime p reduces to 0.
    let p_bytes: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ];
    let e2_p = RuntimeNat::<4>::from_bytes_be(&p_bytes);
    let inputs_p = push_input_sig(&p256, &pk, &e2_p, &macs, av);
    assert_eq!(inputs_p[3], p256.zero());
}

#[test]
fn push_input_hash_rejects_oversized_inputs() {
    let gf2 = Gf2_128Field::new();
    let macs = [0u128; 6];
    let now = b"2025-04-30T00:00:00Z";

    // v7: 31-byte identifier encodes to 33 CBOR bytes (> 32 slot).
    let long_id = req_attr("org.iso.18013.5.1", "a".repeat(31), [0x61, b'x']);
    assert_eq!(
        push_input_hash(7, &gf2, &[long_id], now, &macs, 0),
        Err(HashInputError::AttributeTooLong)
    );

    // v7: 65-byte CBOR value (> 64 slot).
    let long_val = req_attr("org.iso.18013.5.1", "age", [0u8; 65]);
    assert_eq!(
        push_input_hash(7, &gf2, &[long_val], now, &macs, 0),
        Err(HashInputError::AttributeTooLong)
    );

    // v6: combined CBOR encoding > 96 bytes.
    let long_v6 = req_attr("org.iso.18013.5.1", "age", [0u8; 85]);
    assert_eq!(
        push_input_hash(6, &gf2, &[long_v6], now, &macs, 0),
        Err(HashInputError::AttributeTooLong)
    );

    // now > 20 bytes.
    let ok_attr = req_attr("org.iso.18013.5.1", "age", [0x01]);
    assert_eq!(
        push_input_hash(7, &gf2, &[ok_attr], b"2025-04-30T00:00:00Z!", &macs, 0),
        Err(HashInputError::InvalidNow)
    );
}
