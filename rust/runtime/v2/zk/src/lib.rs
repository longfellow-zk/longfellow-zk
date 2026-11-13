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
//! Commit the packed private inputs, packing masks, sumcheck pads, and terminal cells.
//! The joint wrapper adds two fresh private fingerprint masks per field and
//! fixes the selected witness before frontend challenges. Then run sumcheck
//! on the same transcript with the public inputs bound. Its
//! symbolic constraints describe the checks on those hidden values. Reduce the
//! input claim to two packing equations (one direct equation for degree one),
//! then pass all constraints and the circuit ID to Polygero on the same
//! transcript, whose prefix already binds every source message. The runtime
//! constraint compiler substitutes public inputs and maps pads to committed
//! positions, producing sparse A and b for Polygero's A*w+b=0 check.
//!
//! The prover runs numerical sumcheck; the verifier reconstructs its constraints
//! from the messages. Both use the same constraint compiler and codec layout.
//! `context` supplies borrowed field/domain references and trusted circuit
//! metadata. Prover and verifier orchestration remain in separate role modules.
pub(crate) mod context;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod joint;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod packing_commitment;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub use context::{CircuitInput, ZkContext};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod constraint_compiler;
pub use crate::runtime::v2::proto::zk::{CircuitGeometry, ZkProof, ZkProofGeometry};
cfg_prover! { mod prover; pub use prover::{ZkProver, ZkProverCommitment}; }
cfg_verifier! { mod verifier; pub use verifier::{ZkVerifier,ZkVerificationError}; }

#[cfg(test)]
#[path = "../tests/zk.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/layouts.rs"]
mod tests_layouts;
