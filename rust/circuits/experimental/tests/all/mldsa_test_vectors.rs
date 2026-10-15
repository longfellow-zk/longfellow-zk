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

//! Trusted committed C++ fixtures shared by native and in-circuit ML-DSA tests.

fn decode_hex(hex: &str) -> Vec<u8> {
    assert_eq!(hex.len() % 2, 0, "fixture hex must contain whole bytes");
    hex.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digit = |value: u8| match value {
                b'0'..=b'9' => value - b'0',
                b'a'..=b'f' => value - b'a' + 10,
                b'A'..=b'F' => value - b'A' + 10,
                _ => panic!("invalid hex digit"),
            };
            digit(pair[0]) << 4 | digit(pair[1])
        })
        .collect()
}

/// Returns the first fixture's message, public key, context, mu, and signature,
/// in the order used by the committed C++ test vectors.
pub(super) fn first_cpp_example(source: &str, marker: &str) -> Vec<Vec<u8>> {
    let mut cursor = source.find(marker).expect("missing C++ fixture marker");
    let mut result = Vec::new();
    while result.len() < 5 {
        let call = source[cursor..]
            .find("hexToBytes(")
            .expect("missing C++ fixture field")
            + cursor;
        let mut depth = 0;
        let mut end = call;
        for (offset, byte) in source.as_bytes()[call..].iter().enumerate() {
            match byte {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = call + offset;
                        break;
                    }
                }
                _ => {}
            }
        }
        assert!(end > call, "unterminated C++ fixture field");
        let body = &source[call..=end];
        let mut quoted = false;
        let mut hex = String::new();
        for character in body.chars() {
            if character == '"' {
                quoted = !quoted;
            } else if quoted && character.is_ascii_hexdigit() {
                hex.push(character);
            }
        }
        result.push(decode_hex(&hex));
        cursor = end + 1;
    }
    result
}

#[test]
fn fixture_hex_accepts_both_cases() {
    assert_eq!(decode_hex("00aAfF"), [0, 170, 255]);
}

#[test]
#[should_panic(expected = "fixture hex must contain whole bytes")]
fn fixture_hex_rejects_partial_bytes() {
    let _ = decode_hex("abc");
}
