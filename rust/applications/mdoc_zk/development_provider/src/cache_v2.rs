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

use crate::mdoc::{
    circuits::NEXT_VERSION,
    runtime::v2::{
        provider::{self, ProvidedCircuit},
        PolygeroParameters, ZkSpecStruct,
    },
};

const MAGIC: &[u8; 9] = b"MDOCNEXT4";

/// Save a trusted NEXT bundle for reuse by development tools and benchmarks.
pub fn write_next(mut writer: impl Write, circuit: &ProvidedCircuit) -> Result<(), String> {
    let spec = circuit.spec();
    validate(spec)?;
    writer.write_all(MAGIC).map_err(|error| error.to_string())?;
    writer
        .write_all(&spec.combined_hash)
        .map_err(|error| error.to_string())?;
    let h = spec.polygero_hash;
    let s = spec.polygero_sig;
    for value in [
        spec.version,
        spec.num_attributes,
        h.k,
        h.n,
        h.s,
        h.t,
        s.k,
        s.n,
        s.s,
        s.t,
    ] {
        writer
            .write_all(&(value as u64).to_le_bytes())
            .map_err(|error| error.to_string())?;
    }
    let manifest = spec.manifest.to_bytes();
    writer.write_all(&manifest).map_err(|e| e.to_string())?;
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
    let mut values = [0usize; 10];
    for value in &mut values {
        let mut bytes = [0; 8];
        reader
            .read_exact(&mut bytes)
            .map_err(|error| error.to_string())?;
        *value = usize::try_from(u64::from_le_bytes(bytes)).map_err(|error| error.to_string())?;
    }
    let [version, num_attributes, hk, hn, hs, ht, sk, sn, ss, st] = values;
    let spec = ZkSpecStruct {
        combined_hash,
        num_attributes,
        version,
        manifest: {
            let mut bytes = [0; crate::mdoc::proto::packed::HashInputManifest::HEADER_SIZE];
            reader.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            crate::mdoc::proto::packed::HashInputManifest::from_bytes(&bytes)?
        },
        polygero_hash: PolygeroParameters {
            k: hk,
            n: hn,
            s: hs,
            t: ht,
        },
        polygero_sig: PolygeroParameters {
            k: sk,
            n: sn,
            s: ss,
            t: st,
        },
    };
    validate(&spec)?;
    let mut compressed = Vec::new();
    reader
        .read_to_end(&mut compressed)
        .map_err(|error| error.to_string())?;
    provider::from_compressed(spec, compressed)
        .map_err(|error| format!("Invalid NEXT circuit bundle: {error:?}"))
}

fn validate(spec: &ZkSpecStruct) -> Result<(), String> {
    if spec.version != NEXT_VERSION || !(1..=4).contains(&spec.num_attributes) {
        return Err("Cache does not describe a supported NEXT circuit".into());
    }
    Ok(())
}

pub fn write_next_file(path: &std::path::Path, bundle: &ProvidedCircuit) -> Result<(), String> {
    write_next(
        std::fs::File::create(path).map_err(|e| e.to_string())?,
        bundle,
    )
}
pub fn read_next_file(path: &std::path::Path) -> Result<ProvidedCircuit, String> {
    read_next(std::fs::File::open(path).map_err(|e| e.to_string())?)
}
