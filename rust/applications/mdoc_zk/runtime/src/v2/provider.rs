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

//! Longfellow v2 frozen circuit provider. Registry lookup never compiles circuits.

use std::path::Path;

use super::{MdocProverErrorCode, ZkSpecStruct, ZK_SPECS};

/// A trusted v2 specification and its matching compressed archive.
/// Construction checks container metadata; decoding always verifies payload IDs.
/// Read-only access keeps the two stored values together.
#[derive(Clone, Debug)]
pub struct ProvidedCircuit {
    spec: ZkSpecStruct,
    compressed: Vec<u8>,
}

impl ProvidedCircuit {
    pub fn spec(&self) -> &ZkSpecStruct {
        &self.spec
    }

    pub fn compressed(&self) -> &[u8] {
        &self.compressed
    }

    /// Move the pair into a caller that owns its circuit bytes.
    pub fn into_parts(self) -> (ZkSpecStruct, Vec<u8>) {
        (self.spec, self.compressed)
    }
}

/// Load a frozen circuit from the repository's artifact directory.
pub fn materialize(
    version: usize,
    num_attributes: usize,
) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    materialize_from(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("applications/mdoc_zk/artifacts/circuits")
            .as_path(),
        version,
        num_attributes,
    )
}

/// Load a registered circuit from a caller-owned artifact directory.
/// Unknown specifications and missing artifacts are errors; no compiler fallback exists.
pub fn materialize_from(
    directory: &Path,
    version: usize,
    num_attributes: usize,
) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    let spec = ZK_SPECS
        .iter()
        .find(|s| s.version == version && s.num_attributes == num_attributes)
        .ok_or(MdocProverErrorCode::InvalidZkSpecVersion)?;
    load(directory, spec)
}

fn load(directory: &Path, spec: &ZkSpecStruct) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    let path = directory.join(format!("{}.lfa2", spec.combined_hash_hex()));
    let file = std::fs::File::open(path).map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let compressed = super::archive::read_compressed(file)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;
    from_compressed(*spec, compressed)
}

/// Check trusted archive metadata without recomputing circuit payload IDs.
pub(in crate::mdoc) fn from_compressed(
    spec: ZkSpecStruct,
    compressed: Vec<u8>,
) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    if !spec.supports_version() {
        return Err(MdocProverErrorCode::InvalidZkSpecVersion);
    }
    let archive = super::archive::read(&compressed)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;
    if archive.combined_id != spec.combined_hash || archive.circuit_version as usize != spec.version
    {
        return Err(MdocProverErrorCode::HashParsingFailure);
    }
    if archive.entries.len() != 2 || archive.get("sig").is_none() || archive.get("hash").is_none() {
        return Err(MdocProverErrorCode::CircuitParsingFailure);
    }
    Ok(ProvidedCircuit { spec, compressed })
}

/// Enumerate only published, frozen specifications.
pub fn registered_versions_and_attrs() -> Vec<(usize, usize)> {
    ZK_SPECS
        .iter()
        .map(|s| (s.version, s.num_attributes))
        .collect()
}

#[cfg(test)]
#[path = "../../tests/v2_provider.rs"]
mod tests;
