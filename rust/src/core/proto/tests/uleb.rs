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

//! The generic ULEB128 codec decodes the same integer on every host width.

use crate::core::proto::{read_uleb128, serialize_uleb128};

fn read(bytes: &[u8]) -> Result<usize, String> {
    let mut stream = bytes;
    let value = read_uleb128(&mut stream)?;
    assert!(stream.is_empty(), "reader left bytes behind");
    Ok(value)
}

#[test]
fn small_values_round_trip_unchanged() {
    for value in [
        0,
        1,
        127,
        128,
        300,
        0x3FFF,
        0x4000,
        0x0FFF_FFFF,
        u32::MAX as usize,
    ] {
        let mut bytes = Vec::new();
        serialize_uleb128(&mut bytes, value);
        assert_eq!(read(&bytes), Ok(value));
    }
}

#[test]
fn values_above_32_bits_decode_or_are_rejected_by_width() {
    // 2^35, the audit's reproduction: six bytes.
    let bytes = [0x80, 0x80, 0x80, 0x80, 0x80, 0x01];
    let decoded = read(&bytes);
    if usize::BITS >= 64 {
        assert_eq!(decoded.map(|v| v as u64), Ok(1u64 << 35));
    } else {
        assert!(
            decoded.is_err(),
            "a 32-bit host must reject 2^35, got {decoded:?}"
        );
    }
}

#[test]
fn usize_max_round_trips() {
    let mut bytes = Vec::new();
    serialize_uleb128(&mut bytes, usize::MAX);
    assert!(bytes.len() <= 10);
    assert_eq!(read(&bytes), Ok(usize::MAX));
}

#[test]
fn over_long_and_overflowing_encodings_are_errors() {
    // An eleventh byte is never allowed.
    let mut over_long = vec![0x80; 10];
    over_long.push(0x00);
    assert!(read_uleb128(&mut over_long.as_slice()).is_err());
    // A tenth byte may carry only bit 63.
    let mut overflow = vec![0xFF; 9];
    overflow.push(0x02);
    assert!(read_uleb128(&mut overflow.as_slice()).is_err());
    // A truncated encoding is an error, not a panic.
    assert!(read_uleb128(&mut [0x80u8, 0x80].as_slice()).is_err());
    // 2^63 is the largest bit the tenth byte can set.
    let mut top = vec![0x80; 9];
    top.push(0x01);
    let decoded = read(&top);
    if usize::BITS >= 64 {
        assert_eq!(decoded.map(|v| v as u64), Ok(1u64 << 63));
    } else {
        assert!(decoded.is_err());
    }
}
