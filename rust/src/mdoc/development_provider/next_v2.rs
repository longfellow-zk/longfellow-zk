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

//! Compile NEXT with the shared, checked Polygero profile.

use crate::{
    core::proto::{archive::CircuitArchive, v2::CircuitReader},
    mdoc::{
        compile,
        proto::{K_ZSTD_LEVEL, NEXT_MAX_ATTRIBUTES, NEXT_VERSION},
        v2::{
            domains::with_domains,
            provider::{self, ProvidedCircuit},
            ZkSpecStruct, MDOC_JOINT_PROFILE,
        },
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

/// Compile the development circuit and return its matching specification.
/// The saved specification retains the shared proof parameter profile.
pub fn compile_next(num_attributes: usize) -> Result<ProvidedCircuit, String> {
    if !(1..=NEXT_MAX_ATTRIBUTES).contains(&num_attributes) {
        return Err(format!(
            "NEXT supports one to {NEXT_MAX_ATTRIBUTES} attributes"
        ));
    }
    let bytes = compile::compile_circuits(num_attributes)?;
    let archive = crate::core::proto::v2::archive::from_bytes(&bytes)?;
    let spec = specification(&archive, num_attributes)?;
    let compressed =
        zstd::encode_all(bytes.as_slice(), K_ZSTD_LEVEL).map_err(|error| error.to_string())?;
    provider::from_compressed(spec, compressed)
        .map_err(|error| format!("Invalid compiled NEXT bundle: {error:?}"))
}

/// The compiler supplies IDs and circuit structure; offline selection supplies
/// K, N, S and T. The runtime derives all remaining geometry from those choices.
fn specification(archive: &CircuitArchive, num_attributes: usize) -> Result<ZkSpecStruct, String> {
    if archive.circuit_version as usize != NEXT_VERSION {
        return Err("Compiler returned a circuit other than NEXT".into());
    }
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    // Keep payload validation even though the fixed profile does not inspect
    // circuit sizes. The provider separately checks the archive's metadata.
    CircuitReader::new(&f)
        .from_bytes(&archive.get("hash").ok_or("Missing hash circuit")?.payload)?;
    CircuitReader::new(&p).from_bytes(
        &archive
            .get("sig")
            .ok_or("Missing signature circuit")?
            .payload,
    )?;
    // One profile serves both fields and all supported attribute counts, at an
    // ordinary code rate of 1/7. The checked Hahn bounds keep the shared
    // opening and parent charges within the same query budget as the frontend.
    // Validate it against each interpolation domain.
    let config = MDOC_JOINT_PROFILE;
    let fits = with_domains(&f, &p, |(hash, signature)| {
        config.can_interpolate(hash) && config.can_interpolate(signature)
    });
    if !fits {
        return Err("unsupported fixed Polygero profile".into());
    }
    Ok(ZkSpecStruct {
        combined_hash: archive.combined_id,
        num_attributes,
        version: NEXT_VERSION,
        polygero: config,
    })
}

#[cfg(test)]
mod tests;
