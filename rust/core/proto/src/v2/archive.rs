// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Bounded LFA2 loading for v2. The legacy archive readers remain unchanged.
use std::io::BufRead;

use super::limits::*;
use crate::core::proto::{
    archive::{compute_combined_id, ArchiveEntry, CircuitArchive, LFA2_MAGIC, LFA_VERSION},
    v2::uleb::read_size,
};

fn count<R: BufRead>(input: &mut R, max: usize, what: &str) -> Result<usize, String> {
    // Decode independently of the host word size, then check the declared limit.
    let n = read_size(input)?;
    if n > max {
        return Err(format!("V2 archive excessive {what}: {n} > {max}"));
    }
    Ok(n)
}
fn array<T>(n: usize) -> Result<Vec<T>, String> {
    let mut out = Vec::new();
    out.try_reserve_exact(n)
        .map_err(|e| format!("V2 archive allocation failed: {e}"))?;
    Ok(out)
}
fn bytes<R: BufRead>(input: &mut R, n: usize) -> Result<Vec<u8>, String> {
    // Grow only as bytes arrive. A short stream must not zero-fill the full
    // declared payload before reporting EOF; directory limits still bound it.
    let mut out = Vec::new();
    while out.len() < n {
        let available = input.fill_buf().map_err(|e| e.to_string())?;
        let count = available.len().min(n - out.len());
        if count == 0 {
            return Err("Incomplete v2 archive payload".into());
        }
        if count > out.capacity() - out.len() {
            let additional = out.capacity().max(count).min(n - out.len());
            out.try_reserve_exact(additional)
                .map_err(|e| format!("V2 archive allocation failed: {e}"))?;
        }
        out.extend_from_slice(&available[..count]);
        input.consume(count);
    }
    Ok(out)
}
fn text<R: BufRead>(input: &mut R, total: &mut usize) -> Result<String, String> {
    let n = count(input, MAX_METADATA_BYTES, "metadata length")?;
    *total = total
        .checked_add(n)
        .filter(|&sum| sum <= MAX_METADATA_BYTES)
        .ok_or("V2 archive excessive metadata")?;
    String::from_utf8(bytes(input, n)?).map_err(|e| e.to_string())
}
pub fn from_bytes(bytes: &[u8]) -> Result<CircuitArchive, String> {
    let mut input = bytes;
    let archive = from_stream(&mut input)?;
    if !input.is_empty() {
        return Err("Trailing data after v2 archive".into());
    }
    Ok(archive)
}
pub fn from_stream<R: BufRead>(input: &mut R) -> Result<CircuitArchive, String> {
    let mut magic = [0; 4];
    input.read_exact(&mut magic).map_err(|e| e.to_string())?;
    if &magic != LFA2_MAGIC {
        return Err("V2 requires an LFA2 archive".into());
    }
    let mut version = [0];
    input.read_exact(&mut version).map_err(|e| e.to_string())?;
    if version[0] != LFA_VERSION {
        return Err("Unsupported v2 archive version".into());
    }
    let circuit_version = u32::try_from(read_size(input)?).map_err(|e| e.to_string())?;
    let mut combined_id = [0; 32];
    input
        .read_exact(&mut combined_id)
        .map_err(|e| e.to_string())?;
    let mut metadata_bytes = 0;
    let created_at = text(input, &mut metadata_bytes)?;
    let author = text(input, &mut metadata_bytes)?;
    let generator_tool = text(input, &mut metadata_bytes)?;
    let description = text(input, &mut metadata_bytes)?;
    let n = count(input, MAX_ARCHIVE_ENTRIES, "entry count")?;
    // Conservatively include both the entry directory and final entries.
    metadata_bytes = n
        .checked_mul(2 * std::mem::size_of::<ArchiveEntry>())
        .and_then(|size| size.checked_add(metadata_bytes))
        .filter(|&size| size <= MAX_METADATA_BYTES)
        .ok_or("V2 archive excessive metadata")?;
    let mut metadata: Vec<(String, [u8; 32], usize)> = array(n)?;
    let mut total_bytes = 0usize;
    for _ in 0..n {
        let name = text(input, &mut metadata_bytes)?;
        if metadata.iter().any(|entry| entry.0 == name) {
            return Err("Duplicate v2 archive entry".into());
        }
        let mut id = [0; 32];
        input.read_exact(&mut id).map_err(|e| e.to_string())?;
        let size = count(input, MAX_ARCHIVE_BYTES, "payload length")?;
        total_bytes = total_bytes
            .checked_add(size)
            .filter(|&sum| sum <= MAX_ARCHIVE_BYTES)
            .ok_or("V2 archive excessive total payload")?;
        metadata.push((name, id, size));
    }
    // The complete entry directory has passed validation before payload allocation.
    let mut entries = array(n)?;
    for (name, circuit_id, size) in metadata {
        let payload = bytes(input, size)?;
        entries.push(ArchiveEntry {
            name,
            circuit_id,
            payload,
        });
    }
    if compute_combined_id(&entries) != combined_id {
        return Err("Combined archive ID mismatch".into());
    }
    Ok(CircuitArchive {
        version: version[0],
        circuit_version,
        combined_id,
        created_at,
        author,
        generator_tool,
        description,
        entries,
    })
}

#[cfg(test)]
#[path = "../../tests/v2_archive.rs"]
mod tests;
