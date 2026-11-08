// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 compressed artifact loading, shared by circuit loading and providers.
use std::io::{BufRead, Read};

use crate::core::proto::{
    archive::CircuitArchive,
    v2::{archive, limits::*},
};

pub(in crate::mdoc) fn read_compressed(reader: impl Read) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    reader
        .take((MAX_ARCHIVE_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > MAX_ARCHIVE_BYTES {
        return Err("Excessive compressed v2 circuit archive".into());
    }
    Ok(bytes)
}
pub(super) fn read(compressed: &[u8]) -> Result<CircuitArchive, String> {
    if compressed.len() > MAX_ARCHIVE_BYTES {
        return Err("Excessive compressed v2 circuit archive".into());
    }
    let mut decoder = zstd::stream::read::Decoder::new(compressed).map_err(|e| e.to_string())?;
    decoder
        .window_log_max(MAX_METADATA_BYTES.ilog2())
        .map_err(|e| e.to_string())?;
    let mut reader = std::io::BufReader::new(decoder);
    let result = archive::from_stream(&mut reader)?;
    if !reader.fill_buf().map_err(|e| e.to_string())?.is_empty() {
        return Err("Trailing data after circuit archive".into());
    }
    Ok(result)
}

#[cfg(test)]
#[path = "../../tests/v2_archive.rs"]
mod tests;
