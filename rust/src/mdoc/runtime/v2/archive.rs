// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 compressed artifact loading, shared by circuit loading and providers.
use std::io::{BufRead, Read};

use crate::{
    core::proto::{
        archive::{ArchiveEntry, CircuitArchive},
        v2::{archive, limits::*},
    },
    mdoc::v2::ZkSpecStruct,
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
    let mut decoder = zstd::stream::read::Decoder::with_buffer(compressed)
        .map_err(|e| e.to_string())?
        .single_frame();
    decoder
        .window_log_max(MAX_METADATA_BYTES.ilog2())
        .map_err(|e| e.to_string())?;
    let mut reader = std::io::BufReader::new(decoder);
    let result = archive::from_stream(&mut reader)?;
    if !reader.fill_buf().map_err(|e| e.to_string())?.is_empty() {
        return Err("Trailing data after circuit archive".into());
    }
    if !reader.into_inner().finish().is_empty() {
        return Err("Trailing compressed circuit archive data".into());
    }
    Ok(result)
}

/// The `sig` and `hash` entries of an mdoc archive. The archive holds exactly
/// these two, and, given a spec, has its combined ID and circuit version.
/// Callers map the error to their own codes.
pub(super) fn circuit_entries<'a>(
    archive: &'a CircuitArchive,
    spec: Option<&ZkSpecStruct>,
) -> Result<(&'a ArchiveEntry, &'a ArchiveEntry), &'static str> {
    if archive.entries.len() != 2 {
        return Err("V2 archive must contain exactly the signature and hash circuits");
    }
    if let Some(expected) = spec {
        if archive.combined_id != expected.combined_hash
            || archive.circuit_version as usize != expected.version
        {
            return Err("Circuit archive does not match the selected v2 specification");
        }
    }
    let sig = archive
        .get("sig")
        .ok_or("Missing 'sig' entry in circuit archive")?;
    let hash = archive
        .get("hash")
        .ok_or("Missing 'hash' entry in circuit archive")?;
    Ok((sig, hash))
}
