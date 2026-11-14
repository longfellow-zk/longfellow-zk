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

//! Longfellow v1 public-key parsing for application entry points.

use crate::{
    core::algebra::{Nat, SerializableField},
    runtime::algebra::p256::P256Field,
};

fn hex_decode_to_32_bytes_be(s: &str) -> Result<[u8; 32], String> {
    let mut bytes = [0u8; 32];
    let hex_len = s.len();
    if hex_len > 64 {
        return Err("Hex string too long".to_string());
    }

    let mut s_padded = s.to_string();
    if hex_len < 64 {
        s_padded = format!("{s:0>64}");
    }

    for (i, byte) in bytes.iter_mut().enumerate() {
        let high = char_to_digit(s_padded.as_bytes()[2 * i])?;
        let low = char_to_digit(s_padded.as_bytes()[2 * i + 1])?;
        *byte = (high << 4) | low;
    }
    Ok(bytes)
}

fn char_to_digit(c: u8) -> Result<u8, String> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        _ => Err(format!("Invalid hex character: {}", char::from(c))),
    }
}

fn parse_hex_nat<const W: usize, N: Nat<W>>(s: &str) -> Result<N, String> {
    let s_clean = s.strip_prefix("0x").unwrap_or(s);
    let mut bytes_be = hex_decode_to_32_bytes_be(s_clean)?;
    bytes_be.reverse();
    Ok(N::from_bytes_le(&bytes_be))
}

pub(super) fn parse_pk_coordinate(
    s: &str,
    field: &P256Field,
) -> Result<crate::runtime::algebra::p256::P256Element, String> {
    let nat = parse_hex_nat::<4, crate::runtime::algebra::RuntimeNat<4>>(s)?;
    field.bytes_to_element(&nat.to_bytes_le())
}
