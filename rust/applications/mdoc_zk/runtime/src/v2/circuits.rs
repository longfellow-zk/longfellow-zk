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

//! Longfellow v2 trusted circuit loading with opt-in payload ID enforcement.
use std::io::BufRead;

use super::ZkSpecStruct;
use crate::{
    core::proto::{archive::CircuitArchive, circuit::Circuit, reader::CircuitReader, FieldID},
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

type DecodedCircuits = (Circuit<P256Field>, Circuit<Gf2_128Field>);

/// Load trusted circuits; optionally recompute and enforce their payload IDs.
pub fn decompress_circuits(
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
    enforce_circuit_id: bool,
) -> Result<DecodedCircuits, String> {
    load(compressed, p256, gf2, None, enforce_circuit_id)
}

/// Check cheap archive metadata against the spec. Application circuits are trusted;
/// this path deliberately skips recomputing their semantic IDs.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn for_spec(
    spec: &ZkSpecStruct,
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
) -> Result<DecodedCircuits, String> {
    load(compressed, p256, gf2, Some(spec), false)
}

fn load(
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
    spec: Option<&ZkSpecStruct>,
    enforce_circuit_id: bool,
) -> Result<DecodedCircuits, String> {
    let decoder = zstd::stream::read::Decoder::new(compressed)
        .map_err(|e| format!("Failed to initialize zstd decoder: {e}"))?;
    let mut reader = std::io::BufReader::new(decoder);
    let archive = CircuitArchive::from_stream(&mut reader)?;
    if !reader.fill_buf().map_err(|e| e.to_string())?.is_empty() {
        return Err("Trailing data after circuit archive".into());
    }
    if archive.entries.len() != 2 {
        return Err("V2 archive must contain exactly the signature and hash circuits".into());
    }
    if let Some(expected) = spec {
        if archive.combined_id != expected.combined_hash
            || archive.circuit_version as usize != expected.version
        {
            return Err("Circuit archive does not match the selected v2 specification".into());
        }
    }
    let sig_entry = archive
        .get("sig")
        .ok_or("Missing 'sig' entry in circuit archive")?;
    let hash_entry = archive
        .get("hash")
        .ok_or("Missing 'hash' entry in circuit archive")?;
    let (signature, signature_tail) = CircuitReader::new(p256, FieldID::P256)
        .from_bytes(&sig_entry.payload, enforce_circuit_id)?;
    if !signature_tail.is_empty() || signature.id != sig_entry.circuit_id {
        return Err("Signature payload does not match its archive entry".into());
    }
    let (hash, hash_tail) = CircuitReader::new(gf2, FieldID::Gf2_128)
        .from_bytes(&hash_entry.payload, enforce_circuit_id)?;
    if !hash_tail.is_empty() || hash.id != hash_entry.circuit_id {
        return Err("Hash payload does not match its archive entry".into());
    }
    signature.validate_v2()?;
    hash.validate_v2()?;
    Ok((signature, hash))
}

#[cfg(test)]
#[path = "../../tests/v2_circuits.rs"]
mod tests;
