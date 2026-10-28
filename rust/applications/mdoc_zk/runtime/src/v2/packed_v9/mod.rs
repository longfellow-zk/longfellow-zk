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

//! Explicit experimental v9 application API. NEXT and the frozen registry stay v8.
use crate::{mdoc::proto::packed::HashInputManifest, runtime::polygero::PolygeroConfig};
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedV9Spec {
    pub combined_hash: [u8; 32],
    pub num_attributes: usize,
    pub version: usize,
    pub manifest: HashInputManifest,
    pub polygero_hash: super::PolygeroParameters,
    pub polygero_sig: super::PolygeroParameters,
}
impl PackedV9Spec {
    pub fn supports_version(&self) -> bool {
        self.version == 9
            && (1..=4).contains(&self.num_attributes)
            && self.manifest.validate().is_ok()
    }
    pub fn configs(&self) -> (PolygeroConfig, PolygeroConfig) {
        (self.polygero_hash.config(), self.polygero_sig.config())
    }
}
pub mod proto;
pub mod provider;
#[cfg(test)]
#[path = "../../../tests/packed_v9.rs"]
mod tests;
cfg_prover! {
    pub mod prover;
    pub use prover::{run_mdoc_prover, run_mdoc_prover_inner};
}
cfg_verifier! {
    pub mod verifier;
    pub use verifier::{run_mdoc_verifier, run_mdoc_verifier_inner};
}
