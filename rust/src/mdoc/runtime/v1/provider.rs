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

//! Longfellow v1 frozen circuit provider. Registry lookup never compiles circuits.

use std::{io::BufRead, path::Path};

use crate::{
    core::proto::archive::CircuitArchive,
    mdoc::v1::{MdocProverErrorCode, ZkSpecStruct, ZK_SPECS},
};

/// A registered specification and its stored circuit archive.
#[derive(Clone, Debug)]
pub struct ProvidedCircuit {
    pub name: String,
    pub spec: ZkSpecStruct,
    pub archive: CircuitArchive,
    pub compressed: Vec<u8>,
}

/// Load a frozen circuit from the repository's artifact directory.
pub fn materialize(
    version: usize,
    num_attributes: usize,
) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    materialize_from(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/mdoc/artifacts/circuits")
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
    // Preserve the historical archive filename aliases, in their original order.
    for extension in ["lfa2", "lfc2", "v2"] {
        let path = directory.join(format!("{}.{extension}", spec.combined_hash_hex()));
        if let Ok(compressed) = std::fs::read(path) {
            return from_compressed(*spec, compressed);
        }
    }
    Err(MdocProverErrorCode::GeneralFailure)
}

/// Check trusted archive metadata without recomputing circuit payload IDs.
fn from_compressed(
    spec: ZkSpecStruct,
    compressed: Vec<u8>,
) -> Result<ProvidedCircuit, MdocProverErrorCode> {
    let archive = read_archive(&compressed)?;
    if archive.combined_id != spec.combined_hash {
        return Err(MdocProverErrorCode::HashParsingFailure);
    }
    Ok(ProvidedCircuit {
        name: spec.combined_hash_hex(),
        spec,
        archive,
        compressed,
    })
}

/// Decode the container and reject trailing bytes; payload decoding belongs to circuit loading.
fn read_archive(compressed: &[u8]) -> Result<CircuitArchive, MdocProverErrorCode> {
    let decoder = zstd::stream::read::Decoder::new(compressed)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;
    let mut reader = std::io::BufReader::new(decoder);
    let archive = CircuitArchive::from_stream(&mut reader)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;
    if !reader
        .fill_buf()
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?
        .is_empty()
    {
        return Err(MdocProverErrorCode::CircuitParsingFailure);
    }
    Ok(archive)
}

/// Enumerate only published, frozen specifications.
pub fn registered_versions_and_attrs() -> Vec<(usize, usize)> {
    ZK_SPECS
        .iter()
        .map(|s| (s.version, s.num_attributes))
        .collect()
}

#[cfg(test)]
mod tests;
