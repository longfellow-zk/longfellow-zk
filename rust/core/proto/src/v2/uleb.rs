// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Host-independent length decoding for v2 archives.
use std::io::BufRead;

pub(super) fn read_size<R: BufRead>(input: &mut R) -> Result<usize, String> {
    let mut value = 0u64;
    for index in 0..10 {
        let mut byte = [0];
        input.read_exact(&mut byte).map_err(|e| e.to_string())?;
        let payload = u64::from(byte[0] & 0x7f);
        // At bit 63 only one payload bit remains. Check before shifting so
        // neither truncation nor the host's shift behavior can affect parsing.
        if index == 9 && (payload > 1 || byte[0] & 0x80 != 0) {
            return Err("V2 ULEB128 exceeds u64".into());
        }
        value |= payload << (7 * index);
        if byte[0] & 0x80 == 0 {
            return usize::try_from(value).map_err(|_| "V2 ULEB128 exceeds usize".into());
        }
    }
    Err("V2 ULEB128 exceeds u64".into())
}

#[cfg(test)]
#[path = "../../tests/v2_uleb.rs"]
mod tests;
