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

//! Local NEXT cache: save the complete v2 spec with its compressed archive.
//!
//! This is an offline artifact format. Reading it preserves the saved parameter
//! choices and never retunes an old archive using a newer compiler's policy.

use std::io::{Read, Write};

use crate::{
    mdoc::{
        proto::{NEXT_MAX_ATTRIBUTES, NEXT_VERSION},
        v2::{
            archive::read_compressed,
            provider::{self, ProvidedCircuit},
            ZkSpecStruct,
        },
    },
    runtime::v2::proto::polygero::{PolygeroConfig, PolygeroGeometry},
};

/// Version 2 stores the one joint profile; version 1 stored a profile per field.
const MAGIC: &[u8; 9] = b"MDOCNEXT2";

/// Save a trusted NEXT bundle for reuse by development tools and benchmarks.
pub fn write_next(mut writer: impl Write, circuit: &ProvidedCircuit) -> Result<(), String> {
    let spec = circuit.spec();
    validate(spec)?;
    writer.write_all(MAGIC).map_err(|error| error.to_string())?;
    writer
        .write_all(&spec.combined_hash)
        .map_err(|error| error.to_string())?;
    let p = spec.polygero;
    for value in [spec.version, spec.num_attributes, p.k, p.n, p.s, p.t] {
        writer
            .write_all(&(value as u64).to_le_bytes())
            .map_err(|error| error.to_string())?;
    }
    writer
        .write_all(circuit.compressed())
        .map_err(|error| error.to_string())
}

/// Restore the saved spec and archive together. Legacy hash-only caches are rejected.
pub fn read_next(mut reader: impl Read) -> Result<ProvidedCircuit, String> {
    let mut magic = [0; MAGIC.len()];
    reader
        .read_exact(&mut magic)
        .map_err(|error| error.to_string())?;
    if &magic != MAGIC {
        return Err("Not a NEXT circuit bundle".into());
    }
    let mut combined_hash = [0; 32];
    reader
        .read_exact(&mut combined_hash)
        .map_err(|error| error.to_string())?;
    let mut values = [0usize; 6];
    for value in &mut values {
        let mut bytes = [0; 8];
        reader
            .read_exact(&mut bytes)
            .map_err(|error| error.to_string())?;
        *value = usize::try_from(u64::from_le_bytes(bytes)).map_err(|error| error.to_string())?;
    }
    let [version, num_attributes, k, n, s, t] = values;
    let spec = ZkSpecStruct {
        combined_hash,
        num_attributes,
        version,
        polygero: PolygeroConfig { k, s, n, t },
    };
    validate(&spec)?;
    let compressed = read_compressed(reader)?;
    provider::from_compressed(spec, compressed)
        .map_err(|error| format!("Invalid NEXT circuit bundle: {error:?}"))
}

fn validate(spec: &ZkSpecStruct) -> Result<(), String> {
    if spec.version != NEXT_VERSION || !(1..=NEXT_MAX_ATTRIBUTES).contains(&spec.num_attributes) {
        return Err("Cache does not describe a supported NEXT circuit".into());
    }
    PolygeroGeometry::new(0, spec.polygero).map_err(|e| e.to_string())?;
    Ok(())
}
