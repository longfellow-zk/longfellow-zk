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

//! Longfellow v2 execution specifications and the frozen circuit registry.
//!
//! Proving and verification take an explicit spec. Registry lookup discovers only
//! published circuits; development specs are supplied with their compiled archive.

use crate::runtime::polygero::PolygeroConfig;
pub const SYSTEM_ID: &str = "longfellow-libzk-v2";
pub const SUPPORTED_CIRCUIT_VERSIONS: &[usize] = &[9];

/// Independent Polygero choices, fixed for the circuit supplied with this spec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroParameters {
    /// Polynomial dimension: K samples represent degree strictly below K.
    pub k: usize,
    /// Number of committed oracle columns.
    pub n: usize,
    /// Batching-polynomial degree bound, represented by s+1 samples.
    pub s: usize,
    /// Number of distinct columns opened by the verifier.
    pub t: usize,
}
impl PolygeroParameters {
    /// Longfellow v2 uses exactly one private prefix sample per opened column.
    #[must_use]
    pub const fn config(self) -> PolygeroConfig {
        PolygeroConfig {
            k: self.k,
            n: self.n,
            s: self.s,
            t: self.t,
        }
    }
}
/// A v2 spec cannot be supplied to the v1 application entry points.
///
/// ```compile_fail
/// fn accepts(_: &longfellow_zk::mdoc::v1::ZkSpecStruct) {}
/// fn mismatch(spec: &longfellow_zk::mdoc::v2::ZkSpecStruct) { accepts(spec); }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkSpecStruct {
    pub combined_hash: [u8; 32],
    pub num_attributes: usize,
    pub version: usize,
    pub manifest: crate::mdoc::proto::packed::HashInputManifest,
    pub polygero_hash: PolygeroParameters,
    pub polygero_sig: PolygeroParameters,
}
impl ZkSpecStruct {
    /// Whether this runtime can execute the circuit version, independently of publication.
    #[must_use]
    pub fn supports_version(&self) -> bool {
        is_supported_version(self.version)
            && (1..=4).contains(&self.num_attributes)
            && self.manifest.validate().is_ok()
    }
    #[must_use]
    pub const fn configs(&self) -> (PolygeroConfig, PolygeroConfig) {
        (self.polygero_hash.config(), self.polygero_sig.config())
    }
    #[must_use]
    pub fn combined_hash_hex(&self) -> String {
        hash_hex(&self.combined_hash)
    }
}
#[must_use]
pub fn is_supported_version(version: usize) -> bool {
    SUPPORTED_CIRCUIT_VERSIONS.contains(&version)
}
/// Published, frozen v2 circuits. NEXT is supplied by the development provider.
pub const ZK_SPECS: [ZkSpecStruct; 0] = [];
pub const NUM_ZK_SPECS: usize = ZK_SPECS.len();

#[must_use]
pub fn find_zk_spec(system: &str, hash: &[u8; 32]) -> Option<&'static ZkSpecStruct> {
    if system != SYSTEM_ID {
        return None;
    }
    ZK_SPECS.iter().find(|spec| &spec.combined_hash == hash)
}
#[must_use]
pub fn find_zk_spec_by_hex(system: &str, hash: &str) -> Option<&'static ZkSpecStruct> {
    if system != SYSTEM_ID {
        return None;
    }
    ZK_SPECS
        .iter()
        .find(|spec| spec.combined_hash_hex() == hash)
}

/// Format the circuit identifier without relying on another system's helpers.
fn hash_hex(hash: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(64);
    for byte in hash {
        write!(&mut out, "{byte:02x}").unwrap();
    }
    out
}
