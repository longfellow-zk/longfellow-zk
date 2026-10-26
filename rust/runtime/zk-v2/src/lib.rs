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

//! Longfellow v2 composes projective sumcheck with nonrecursive Polygero.
//!
//! Commit the private circuit inputs, sumcheck pads, and final-claim pad products.
//! Then run sumcheck on the same transcript with the public inputs bound. Its
//! symbolic constraints describe the checks on those hidden values. Sample a
//! domain-separated statement identifier from the completed transcript, then
//! compile those constraints and pass the identifier to Polygero. The runtime
//! constraint compiler substitutes public inputs and maps pads to committed
//! positions, producing sparse A and b for Polygero's A*w+b=0 check.
//!
//! The prover runs numerical sumcheck; the verifier reconstructs its constraints
//! from the messages. Both use the same constraint compiler and codec layout.
//! `context` supplies borrowed field/domain references and trusted circuit
//! metadata. Prover and verifier orchestration remain in separate role modules.
mod context;
#[cfg(all(
    feature = "experimental",
    any(test, feature = "prover", feature = "verifier")
))]
pub mod packed;
pub use context::ZkContext;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod constraint_compiler;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub use crate::runtime::proto::zk_v2::{witness_and_constraint_count, ZkProof, ZkProofGeometry};
cfg_prover! { mod prover; pub use prover::{ZkProver, ZkProverCommitment}; }
cfg_verifier! { mod verifier; pub use verifier::{ZkVerifier,ZkVerificationError}; }

#[cfg(test)]
#[path = "../tests/zk.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/layouts.rs"]
mod tests_layouts;
