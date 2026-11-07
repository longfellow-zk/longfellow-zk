// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Canonical field decoding for every v2 proof message.
use std::io::{Error, ErrorKind, Result};

use crate::core::algebra::SerializableField;

/// A field decoder may accept aliases; v2 proof messages must use the unique
/// encoding emitted by the field. Advance the input only after checking it.
pub(crate) fn read_field<F: SerializableField>(bytes: &mut &[u8], f: &F) -> Result<F::E> {
    let width = f.serialized_size_bytes();
    if width == 0 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "zero field encoding width",
        ));
    }
    let raw = bytes
        .get(..width)
        .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "proof field element"))?;
    let value = f
        .bytes_to_element(raw)
        .map_err(|e| Error::new(ErrorKind::InvalidData, e))?;
    if f.to_bytes(&value) != raw {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "noncanonical field element",
        ));
    }
    *bytes = &bytes[width..];
    Ok(value)
}
