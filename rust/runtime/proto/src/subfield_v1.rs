// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1-only compact subfield element encoding.
use std::io::{Error, ErrorKind, Result};

use crate::runtime::algebra::SubfieldV1;

pub fn write_subfield_elt_v1<SF: SubfieldV1>(
    bytes: &mut Vec<u8>,
    x: &SF::E,
    sf: &SF,
) -> Result<()> {
    if !sf.contains(x) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "element not in subfield",
        ));
    }
    let len = sf.serialized_size_bytes();
    let start = bytes.len();
    bytes.resize(start + len, 0);
    sf.to_bytes_into(x, &mut bytes[start..]);
    Ok(())
}

/// Helper to read a subfield element.
pub fn read_subfield_elt_v1<SF: SubfieldV1>(bytes: &mut &[u8], sf: &SF) -> Result<SF::E> {
    let size = sf.serialized_size_bytes();
    if size > bytes.len() {
        return Err(Error::new(
            ErrorKind::UnexpectedEof,
            "EOF reading subfield element",
        ));
    }
    let (chunk, rem) = bytes.split_at(size);
    *bytes = rem;
    let elt = sf.bytes_to_element(chunk).map_err(|e| {
        Error::new(
            ErrorKind::InvalidData,
            format!("Failed to parse subfield element: {e:?}"),
        )
    })?;
    let mut canonical = vec![0u8; size];
    sf.to_bytes_into(&elt, &mut canonical);
    if canonical.as_slice() != chunk {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Non-canonical subfield element encoding",
        ));
    }
    Ok(elt)
}
