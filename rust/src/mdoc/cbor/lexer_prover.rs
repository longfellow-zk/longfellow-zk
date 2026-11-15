// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Honest witness construction; the circuit independently checks every step.

#[derive(Clone, Debug)]
pub struct ConcreteWitness {
    pub remaining: Vec<u64>,
    pub(crate) range: std::ops::Range<usize>,
    pub(crate) headers: Vec<bool>,
    pub(crate) arities: Vec<u64>,
    pub(crate) maps: Vec<bool>,
}

impl ConcreteWitness {
    pub fn derive(bytes: &[u8], actual_len: usize) -> Result<Self, &'static str> {
        Self::derive_range(bytes, 0, actual_len)
    }

    pub fn derive_range(bytes: &[u8], start: usize, end: usize) -> Result<Self, &'static str> {
        if start > end || end > bytes.len() {
            return Err("invalid CBOR range");
        }
        let mut result = Self {
            remaining: vec![0; bytes.len()],
            range: start..end,
            headers: vec![false; bytes.len()],
            arities: vec![0; bytes.len()],
            maps: vec![false; bytes.len()],
        };
        let mut pos = start;
        while pos < end {
            let byte = bytes[pos];
            let major = byte >> 5;
            let info = byte & 31;
            let argument_bytes = match info {
                0..=23 => 0,
                24 => 1,
                25 => 2,
                26 => 4,
                27 => 8,
                _ => return Err("indefinite/reserved CBOR header"),
            };
            if (matches!(major, 2..=5) && info > 25) || (major == 7 && !(20..=23).contains(&info)) {
                return Err("unsupported CBOR token");
            }
            let head_end = pos + 1 + argument_bytes;
            if head_end > end {
                return Err("truncated CBOR argument");
            }
            let argument = if argument_bytes == 0 {
                u64::from(info)
            } else {
                bytes[pos + 1..head_end]
                    .iter()
                    .fold(0, |a, b| (a << 8) | u64::from(*b))
            };
            let arity = match major {
                4 => argument,
                5 => 2 * argument,
                6 => 1,
                _ => 0,
            };
            if matches!(major, 2..=5)
                && (argument > bytes.len() as u64 || arity > bytes.len() as u64)
            {
                return Err("CBOR count exceeds capacity");
            }
            let token_end = head_end
                + if matches!(major, 2 | 3) {
                    argument as usize
                } else {
                    0
                };
            if token_end > end {
                return Err("truncated CBOR string");
            }
            result.headers[pos] = true;
            result.arities[pos] = arity;
            result.maps[pos] = major == 5;
            for i in pos..token_end {
                result.remaining[i] = (token_end - i - 1) as u64;
            }
            pos = token_end;
        }
        Ok(result)
    }
}
