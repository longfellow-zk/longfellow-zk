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

//! Authenticated three-entry v9 circuit bundles.
use super::PackedV9Spec;
use crate::{
    core::proto::{
        archive::{compute_combined_id, CircuitArchive},
        circuit::Circuit,
        reader::CircuitReader,
        FieldID,
    },
    mdoc::proto::packed::HashInputManifest,
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
#[derive(Clone, Debug)]
pub struct ProvidedCircuit {
    spec: PackedV9Spec,
    compressed: Vec<u8>,
}
impl ProvidedCircuit {
    pub fn spec(&self) -> &PackedV9Spec {
        &self.spec
    }
    pub fn compressed(&self) -> &[u8] {
        &self.compressed
    }
    pub fn into_parts(self) -> (PackedV9Spec, Vec<u8>) {
        (self.spec, self.compressed)
    }
}
pub fn from_compressed(spec: PackedV9Spec, compressed: Vec<u8>) -> Result<ProvidedCircuit, String> {
    load(&spec, &compressed, &P256Field::new(), &Gf2_128Field::new())?;
    Ok(ProvidedCircuit { spec, compressed })
}
pub fn load(
    spec: &PackedV9Spec,
    compressed: &[u8],
    p: &P256Field,
    f: &Gf2_128Field,
) -> Result<(Circuit<P256Field>, Circuit<Gf2_128Field>), String> {
    load_inner(spec, compressed, p, f, true)
}
/// Application archives are trusted, as in v8. Authenticate metadata and the
/// domain manifest on each invocation; bundle construction checks payload IDs.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn load_trusted(
    spec: &PackedV9Spec,
    compressed: &[u8],
    p: &P256Field,
    f: &Gf2_128Field,
) -> Result<(Circuit<P256Field>, Circuit<Gf2_128Field>), String> {
    load_inner(spec, compressed, p, f, false)
}
fn load_inner(
    spec: &PackedV9Spec,
    compressed: &[u8],
    p: &P256Field,
    f: &Gf2_128Field,
    enforce_circuit_id: bool,
) -> Result<(Circuit<P256Field>, Circuit<Gf2_128Field>), String> {
    if !spec.supports_version() {
        return Err("invalid packed v9 spec".into());
    }
    use std::io::BufRead;
    let decoder = zstd::stream::read::Decoder::new(compressed).map_err(|e| e.to_string())?;
    let mut reader = std::io::BufReader::new(decoder);
    let a = CircuitArchive::from_stream(&mut reader)?;
    if !reader.fill_buf().map_err(|e| e.to_string())?.is_empty() {
        return Err("trailing v9 archive bytes".into());
    }
    if a.circuit_version != 9
        || a.combined_id != spec.combined_hash
        || a.combined_id != compute_combined_id(&a.entries)
        || a.entries.len() != 3
        || a.entries
            .iter()
            .map(|e| e.name.as_str())
            .collect::<Vec<_>>()
            != ["sig", "hash", "hash-input"]
    {
        return Err("v9 archive metadata mismatch".into());
    }
    let m = &a.entries[2];
    let manifest = HashInputManifest::from_bytes(&m.payload)?;
    if manifest != spec.manifest || manifest.digest() != m.circuit_id {
        return Err("v9 manifest mismatch".into());
    }
    let (sig, st) = CircuitReader::new(p, FieldID::P256)
        .from_bytes(&a.entries[0].payload, enforce_circuit_id)?;
    let (hash, ht) = CircuitReader::new(f, FieldID::Gf2_128)
        .with_total_term_limit(crate::mdoc::proto::packed::V9_MAX_TOTAL_TERMS)
        .from_bytes(&a.entries[1].payload, enforce_circuit_id)?;
    if !st.is_empty()
        || !ht.is_empty()
        || sig.id != a.entries[0].circuit_id
        || hash.id != a.entries[1].circuit_id
        || hash.raw.npublic_input != manifest.public_bits
        || hash.raw.ninput != manifest.public_bits + manifest.private_bits
        || hash.raw.subfield_boundary != 0
    {
        return Err("v9 circuit/domain mismatch".into());
    }
    sig.validate_v2()?;
    hash.validate_v2()?;
    Ok((sig, hash))
}
