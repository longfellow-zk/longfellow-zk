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

//! Application circuit selection: load frozen circuits or compile NEXT.
//!
//! This compiler-enabled module sits above the runtime providers. NEXT produces
//! an owned v2 spec together with its archive; it is never inserted into a frozen
//! registry. Proving and verification consume that pair through the usual v2 API.

use crate::mdoc::runtime::{v1, v2};
mod cache_v2;
mod next_v2;
pub use cache_v2::{read_next, read_next_file, write_next, write_next_file};
pub use next_v2::{compile_next, compile_next_with_classes};

/// Explicit selection keeps development compilation distinct from frozen lookup.
pub enum CircuitRequest {
    FrozenV1 {
        version: usize,
        num_attributes: usize,
    },
    FrozenV2 {
        version: usize,
        num_attributes: usize,
    },
    Next {
        num_attributes: usize,
    },
}

/// The system remains explicit; each variant has its own spec and proof API.
pub enum ProvidedCircuit {
    V1(v1::provider::ProvidedCircuit),
    V2(v2::provider::ProvidedCircuit),
}

/// Delegate frozen requests; compile explicit NEXT or experimental versioned requests.
pub fn materialize(request: CircuitRequest) -> Result<ProvidedCircuit, String> {
    match request {
        CircuitRequest::FrozenV1 {
            version,
            num_attributes,
        } => v1::provider::materialize(version, num_attributes)
            .map(ProvidedCircuit::V1)
            .map_err(|error| format!("Frozen v1 circuit: {error:?}")),
        CircuitRequest::FrozenV2 {
            version,
            num_attributes,
        } => v2::provider::materialize(version, num_attributes)
            .map(ProvidedCircuit::V2)
            .map_err(|error| format!("Frozen v2 circuit: {error:?}")),
        CircuitRequest::Next { num_attributes } => {
            compile_next(num_attributes).map(ProvidedCircuit::V2)
        }
    }
}

#[cfg(test)]
#[path = "../tests/provider.rs"]
mod tests;
