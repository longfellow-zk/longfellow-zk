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
//! Commit the packed private inputs, sumcheck pads and terminal cells, then packing masks.
//! The joint wrapper adds two fresh private fingerprint masks per field and
//! fixes the selected witness before frontend challenges. Then run sumcheck
//! on the same transcript with the public inputs bound. Its
//! symbolic constraints describe the checks on those hidden values. Reduce the
//! input claim to two packing equations (one direct equation for degree one),
//! then pass all constraints, stamped with the session they were derived on,
//! to Polygero on the same transcript, whose prefix already binds every source
//! message and the circuit IDs. The runtime
//! constraint compiler substitutes public inputs and maps pads to committed
//! positions, producing sparse A and b for Polygero's A*w+b=0 check.
//!
//! The prover runs numerical sumcheck; the verifier reconstructs its constraints
//! from the messages. Both use the same constraint compiler and codec layout.
//! `context` derives the layout from the circuit; a participant keeps the
//! field of the interpolation domain it was built with, and every frontend
//! takes its field from its participant. Prover and verifier orchestration
//! remain in separate role modules.
//!
//! Every type the standalone role APIs return has one public path here:
//!
//! ```
//! use longfellow_zk::runtime::{
//!     algebra::p256::P256Field,
//!     v2::zk::{ZkProofStatement, ZkProverCommitment, ZkVerificationError},
//! };
//! fn _named(
//!     _: ZkProofStatement<'_, P256Field>,
//!     _: ZkProverCommitment<'_, P256Field>,
//!     _: ZkVerificationError,
//! ) {
//! }
//! ```
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod batching;
pub(crate) mod context;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod joint;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod packing_commitment;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod split;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod storage;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub use context::CircuitInput;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use context::InputLayout;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use context::{VirtualInput, VirtualInputs};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use transcript::write_joint_geometry;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use transcript::ZkProofStatement;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod constraint_compiler;
cfg_prover! { mod joint_prover; pub(crate) use joint_prover::JointProver; }
cfg_verifier! { mod joint_verifier; pub(crate) use joint_verifier::Authenticated; }
cfg_prover! {
    mod prover;
    pub(crate) use prover::{prove, prove_split};
    pub use prover::{ZkProver, ZkProverCommitment};
}
cfg_verifier! {
    mod verifier;
    pub(crate) use verifier::{reduce, reduce_split};
    pub use verifier::{ZkVerificationError, ZkVerifier};
}

#[cfg(test)]
mod tests;
