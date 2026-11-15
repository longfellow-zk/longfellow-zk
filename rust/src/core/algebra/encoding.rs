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

//! Canonical serializations that compile time and run time share.
//!
//! An element of a prime field is the little-endian encoding of its residue
//! below the modulus; an element of GF(2^128) is the 16 little-endian bytes of
//! its coordinates in the polynomial basis. Zero is all zeros and one is
//! `[1, 0, ...]`. Compile-time and run-time fields implement these encodings
//! independently, and tests check both against the definitions here. The
//! curve constants are canonical encodings of the secp256r1 parameters (SEC 2,
//! FIPS 186-5).

use super::{
    fp24::{BASE_SERIALIZED_SIZE, Q, SERIALIZED_SIZE},
    BareField, FieldID, SerializableField,
};

/// Little-endian bytes of a big-endian hexadecimal constant of `2 * N` digits.
const fn le_from_be_hex<const N: usize>(hex: &str) -> [u8; N] {
    const fn digit(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            _ => panic!("not a lowercase hexadecimal digit"),
        }
    }
    let digits = hex.as_bytes();
    assert!(digits.len() == 2 * N, "wrong constant length");
    let mut out = [0u8; N];
    let mut i = 0;
    while i < N {
        out[N - 1 - i] = digit(digits[2 * i]) << 4 | digit(digits[2 * i + 1]);
        i += 1;
    }
    out
}

/// The P-256 base-field modulus p = 2^256 - 2^224 + 2^192 + 2^96 - 1.
pub const P256_MODULUS: [u8; 32] =
    le_from_be_hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
/// -1 in the P-256 base field, p - 1.
pub const P256_MONE: [u8; 32] =
    le_from_be_hex("ffffffff00000001000000000000000000000000fffffffffffffffffffffffe");
/// The order n of the secp256r1 group, the modulus of its scalar field.
pub const P256_ORDER: [u8; 32] =
    le_from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
/// -1 in the secp256r1 scalar field, n - 1.
pub const P256_ORDER_MONE: [u8; 32] =
    le_from_be_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
/// secp256r1 coefficient a = -3 in the base field.
pub const SECP256R1_A: [u8; 32] =
    le_from_be_hex("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc");
/// secp256r1 coefficient b.
pub const SECP256R1_B: [u8; 32] =
    le_from_be_hex("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b");
/// x coordinate of the secp256r1 generator.
pub const SECP256R1_GX: [u8; 32] =
    le_from_be_hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296");
/// y coordinate of the secp256r1 generator.
pub const SECP256R1_GY: [u8; 32] =
    le_from_be_hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5");

/// A field seen only through its canonical encoding: an element is its bytes.
/// Decoding checks canonicity, so codecs can read circuits and proofs without
/// either side's arithmetic.
///
/// This is a serialization view, not an arithmetic field. Its element type is a
/// plain byte array, so it can hold values that are not field elements; only
/// arrays produced or accepted by `bytes_to_element` are canonical encodings
/// (for a prime field, little-endian integers below the modulus). An array
/// built directly is not validated.
#[derive(Clone, Copy, Debug)]
pub struct Encoding<const N: usize> {
    id: FieldID,
    binary: bool,
    /// Exclusive bound on a prime field's encoding; None for GF(2^128).
    modulus: Option<[u8; N]>,
    mone: [u8; N],
}

/// The P-256 base field.
pub const P256: Encoding<32> = Encoding {
    id: FieldID::P256,
    binary: false,
    modulus: Some(P256_MODULUS),
    mone: P256_MONE,
};

/// The secp256r1 scalar field. It has no circuit field identifier.
pub const P256_SCALAR: Encoding<32> = Encoding {
    id: FieldID::None,
    binary: false,
    modulus: Some(P256_ORDER),
    mone: P256_ORDER_MONE,
};

/// GF(2^128); every 16-byte string is canonical, and -1 = 1.
pub const GF2_128: Encoding<16> = Encoding {
    id: FieldID::Gf2_128,
    binary: true,
    modulus: None,
    mone: le_from_be_hex("00000000000000000000000000000001"),
};

/// `a < b` for little-endian byte strings of equal length.
fn less_le(a: &[u8], b: &[u8]) -> bool {
    a.iter().rev().cmp(b.iter().rev()).is_lt()
}

impl<const N: usize> BareField for Encoding<N> {
    type E = [u8; N];
}

impl<const N: usize> SerializableField for Encoding<N> {
    fn is_binary(&self) -> bool {
        self.binary
    }
    fn serialized_size_bytes(&self) -> usize {
        N
    }
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        dst[..N].copy_from_slice(e);
    }
    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        let e: [u8; N] = bytes
            .try_into()
            .map_err(|_| format!("field element must be {N} bytes"))?;
        if let Some(modulus) = &self.modulus {
            if !less_le(&e, modulus) {
                return Err("field element is not below the modulus".to_string());
            }
        }
        Ok(e)
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.mone.to_vec()
    }
    fn field_id(&self) -> FieldID {
        self.id
    }
}

impl FieldID {
    /// Identify a prime field from its canonical encoding of -1, which
    /// determines the modulus. Primes without a listed identifier map to `None`.
    pub fn of_prime_field(mone: &[u8]) -> Self {
        if mone == P256_MONE {
            Self::P256
        } else {
            Self::None
        }
    }
}

/// The sextic field's agreed wire representation: six little-endian prime
/// coordinates of three bytes each, all strictly below the ML-DSA prime.
/// This type supplies no arithmetic and cannot be used as a runtime field.
#[derive(Clone, Copy, Debug)]
pub struct Fp24Ext6Encoding;

pub const FP24_EXT6: Fp24Ext6Encoding = Fp24Ext6Encoding;

impl BareField for Fp24Ext6Encoding {
    type E = [u8; SERIALIZED_SIZE];
}
impl SerializableField for Fp24Ext6Encoding {
    fn field_id(&self) -> FieldID {
        FieldID::Fp24Ext6
    }
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        SERIALIZED_SIZE
    }
    fn to_bytes_into(&self, value: &Self::E, out: &mut [u8]) {
        out.copy_from_slice(value);
    }
    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        let value: Self::E = bytes
            .try_into()
            .map_err(|_| "Fp24 sextic encoding must contain 18 bytes")?;
        for coordinate in value.as_chunks::<BASE_SERIALIZED_SIZE>().0 {
            let integer = u32::from_le_bytes([coordinate[0], coordinate[1], coordinate[2], 0]);
            if integer >= Q {
                return Err("Fp24 sextic coordinate is not below the modulus".into());
            }
        }
        Ok(value)
    }
    fn serialized_mone(&self) -> Vec<u8> {
        let mut bytes = vec![0; SERIALIZED_SIZE];
        bytes[..BASE_SERIALIZED_SIZE]
            .copy_from_slice(&(Q - 1).to_le_bytes()[..BASE_SERIALIZED_SIZE]);
        bytes
    }
}
