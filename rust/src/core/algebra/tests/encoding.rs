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

//! Compile-time and run-time fields and curves follow the core encodings.

use crate::{
    compile::algebra as compile,
    core::algebra::{
        ec::Curve,
        encoding::{
            Encoding, GF2_128, P256, P256_MODULUS, P256_MONE, P256_ORDER, P256_ORDER_MONE,
            P256_SCALAR, SECP256R1_A, SECP256R1_B, SECP256R1_GX, SECP256R1_GY,
        },
        Gf2_128Field, Nat, SerializableField,
    },
    runtime::algebra as runtime,
};

/// `x + 1` for a little-endian byte string, wrapping.
fn add_one(x: &[u8]) -> Vec<u8> {
    let mut y = x.to_vec();
    for byte in &mut y {
        let (sum, carry) = byte.overflowing_add(1);
        *byte = sum;
        if !carry {
            break;
        }
    }
    y
}

fn assert_same_encoding<F: SerializableField, const N: usize>(f: &F, e: &Encoding<N>) {
    assert_eq!(f.field_id(), e.field_id());
    assert_eq!(f.is_binary(), e.is_binary());
    assert_eq!(f.serialized_size_bytes(), N);
    assert_eq!(f.serialized_mone(), e.serialized_mone());
    let mone = e.serialized_mone();
    let mut one = vec![0; N];
    one[0] = 1;
    // Zero, one, the largest residue, the modulus and the all-ones string.
    for bytes in [vec![0; N], one, mone.clone(), add_one(&mone), vec![0xff; N]] {
        let canonical = e.bytes_to_element(&bytes).is_ok();
        match f.bytes_to_element(&bytes) {
            Ok(x) => {
                assert!(canonical, "{bytes:02x?} decoded but is not canonical");
                assert_eq!(f.to_bytes(&x), bytes);
            }
            Err(_) => assert!(!canonical, "{bytes:02x?} is canonical but was rejected"),
        }
    }
}

#[test]
fn encodings_are_self_consistent() {
    assert_eq!(add_one(&P256_MONE), P256_MODULUS);
    assert_eq!(add_one(&P256_ORDER_MONE), P256_ORDER);
    assert!(P256.bytes_to_element(&P256_MONE).is_ok());
    assert!(P256.bytes_to_element(&P256_MODULUS).is_err());
    assert!(P256_SCALAR.bytes_to_element(&P256_ORDER).is_err());
    let mut one = [0; 16];
    one[0] = 1;
    assert_eq!(GF2_128.serialized_mone(), one);
    assert!(GF2_128.bytes_to_element(&[0xff; 16]).is_ok());
    assert!(GF2_128.bytes_to_element(&[0; 15]).is_err());
}

#[test]
fn fields_follow_the_core_encodings() {
    assert_same_encoding(&compile::p256::P256Field::new(), &P256);
    assert_same_encoding(&runtime::p256::P256Field::new(), &P256);
    assert_same_encoding(&compile::q256::Q256Field::new(), &P256_SCALAR);
    assert_same_encoding(&runtime::q256::Q256Field::new(), &P256_SCALAR);
    assert_same_encoding(&compile::gf2_128::Gf2_128Field::new(), &GF2_128);
    assert_same_encoding(&runtime::gf2_128::Gf2_128Field::new(), &GF2_128);
    assert_same_encoding(&Gf2_128Field::new(), &GF2_128);
}

fn assert_secp256r1<F: SerializableField, C: Curve<4, F = F>>(f: &F, curve: &C) {
    assert_eq!(f.to_bytes(curve.a()), SECP256R1_A);
    assert_eq!(f.to_bytes(curve.b()), SECP256R1_B);
    assert_eq!(f.to_bytes(&curve.g().0), SECP256R1_GX);
    assert_eq!(f.to_bytes(&curve.g().1), SECP256R1_GY);
    assert_eq!(curve.order().to_bytes_le(), P256_ORDER);
}

#[test]
fn curves_follow_the_core_constants() {
    let compile_field = compile::p256::P256Field::new();
    assert_secp256r1(
        &compile_field,
        &compile::secp256r1::Secp256r1::new(&compile_field),
    );
    let runtime_field = runtime::p256::P256Field::new();
    assert_secp256r1(
        &runtime_field,
        &runtime::secp256r1::Secp256r1::new(&runtime_field),
    );
}
