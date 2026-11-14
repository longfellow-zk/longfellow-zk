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

//! Longfellow v1 application API and its own specification registry.

mod attribute;
mod circuits;
mod error;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod inputs;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod key;
pub mod proto;
pub mod zk_spec;
pub use attribute::{req_attr, RequestedAttribute};
pub use circuits::decompress_circuits;
pub use error::{MdocProverErrorCode, MdocVerifierErrorCode};
pub use proto::{MdocProof, MdocProofGeometry};
pub use zk_spec::{
    find_zk_spec, find_zk_spec_by_hex, is_supported_version, ligero_configs, ZkSpecStruct,
    NUM_ZK_SPECS, SYSTEM_ID, ZK_SPECS,
};

pub mod provider;
cfg_prover! { mod mac; pub mod prover; pub use prover::{run_mdoc_prover,run_mdoc_prover_inner}; }
cfg_verifier! { pub mod verifier; pub use verifier::{run_mdoc_verifier,run_mdoc_verifier_inner}; }
