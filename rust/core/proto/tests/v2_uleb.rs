// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::read_size;

fn encode(mut value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (value & 127) as u8;
        value >>= 7;
        out.push(byte | if value == 0 { 0 } else { 128 });
        if value == 0 {
            return out;
        }
    }
}
#[test]
fn length_decoding_checks_host_conversion_after_u64_decoding() {
    for value in [
        0,
        1,
        127,
        128,
        1 << 28,
        u32::MAX as u64,
        1 << 32,
        1 << 35,
        u64::MAX,
    ] {
        let bytes = encode(value);
        for capacity in [1, 16] {
            let mut input = std::io::BufReader::with_capacity(capacity, bytes.as_slice());
            match usize::try_from(value) {
                Ok(expected) => assert_eq!(read_size(&mut input).unwrap(), expected),
                Err(_) => assert!(read_size(&mut input).unwrap_err().contains("usize")),
            }
        }
    }
}
#[test]
fn length_decoding_rejects_u64_overflow_and_unterminated_values() {
    for end in [2, 0x80, 0x81, 0xff] {
        let mut bytes = vec![0x80; 9];
        bytes.push(end);
        assert!(read_size(&mut bytes.as_slice()).is_err());
    }
    for length in 0..10 {
        assert!(read_size(&mut vec![0x80; length].as_slice()).is_err());
    }
}
