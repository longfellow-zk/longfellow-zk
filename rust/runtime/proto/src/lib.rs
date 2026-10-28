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

//! Protocol declarations only. Each system owns its sumcheck and combined-proof codec.
//! Shared Merkle messages and scalar I/O have no system-specific semantics.
//! Fields must describe messages or metadata used by both prover and verifier.
//! Private witness data and role-specific allocation sizes belong to their protocols.

pub mod dual_packing;
pub mod ligero;
pub mod merkle;
pub mod polygero;
pub mod sumcheck_v1;
pub mod sumcheck_v2;
pub mod util;
pub mod zk_v1;
pub mod zk_v2;

pub use ligero::{LigeroCommitment, LigeroGeometry, LigeroProof};
pub use merkle::{Digest, MerkleNonce, MerkleProof, DIGEST_LEN, NONCE_LEN};

#[cfg(test)]
#[path = "../tests/proto_v1.rs"]
mod tests_proto_v1;

#[cfg(test)]
#[path = "../tests/proto_v2.rs"]
mod tests_proto_v2;

#[cfg(test)]
#[path = "../tests/polygero.rs"]
mod tests_polygero;
