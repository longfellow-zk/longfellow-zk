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

//! Multi-field Polygero for Longfellow v2.
//!
//! Participants are recursive `(Participant, Tail)` tuples ending in `()`.
//! Each field has its own encoded rows, masks and H/Z
//! responses. All participants share k/s/n/t and one salted column Merkle tree.
//! No statement is absorbed: `prove` and `reduce` take the statements, draw
//! the batching weights at the boundary after the last message every
//! statement is derived from and use them at once (transcript I8), and
//! every H/Z response is absorbed before a single ordered set of column
//! queries is drawn.
//! A one-field invocation uses `(participant, ())` through the same API.
//!
//! `prover` and `verifier` own their field equations; `prover_commitment` encodes masked
//! rows, `joint` coordinates tuples, `participant` traverses them (each with a prover and a
//! verifier half, `ProverParticipants` and `VerifierParticipants`), and `transcript`
//! owns message framing and challenge rounds. V2 Merkle owns the column authentication codecs and
//! tree. Typed field bodies and the Merkle envelope live in runtime::v2::proto::polygero.
//! Frontends derive A*w+b=0 from their previously absorbed source messages and
//! challenges. Tests and tools may build a static system with
//! `LinearStatement::new`; the transcript does not bind it.
//! Parameter catalogs bound each field separately. Because all fields share one
//! query set, the certified mdoc analysis charges a single joint active-family
//! budget (formal `Soundness.Rate7.parentBudget`, built on `ParameterBounds.parentBudget`). Summing
//! the per-field failure bounds, without assuming independence, is a valid but looser
//! alternative. The former single-field API and PLG9 format have been removed.
mod config;
pub use config::PolygeroLinearTerm;

cfg_role! {
    mod constraints;
    mod error;
    mod joint;
    mod param;
    mod participant;
    mod polynomials;
    mod transcript;
    use crate::runtime::v2::merkle::hash;
    use error::ensure;
    // Outside the crate the bare joint commitment (its parameters, the raw
    // passes over a participant list and the bare prover and verifier) runs
    // only in tests, tools and benchmarks, through the `_for_test` entry
    // points. Complete proofs reach it through `zk` and `mdoc`.
    #[cfg(feature = "testonly")]
    pub use error::PolygeroError;
    #[cfg(not(feature = "testonly"))]
    pub(crate) use error::PolygeroError;
    #[cfg(feature = "testonly")]
    pub use joint::{FieldChallenges, JointPolygeroParam, LinearStatement, Participant, Participants};
    #[cfg(not(feature = "testonly"))]
    pub(crate) use joint::{JointPolygeroParam, LinearStatement, Participant, Participants};
    #[cfg(feature = "testonly")]
    pub use param::PolygeroParam;
    #[cfg(not(feature = "testonly"))]
    pub(crate) use param::PolygeroParam;
}
cfg_prover! {
    mod prover;
    mod prover_commitment;
    #[cfg(feature = "testonly")]
    pub use joint::prover::ProverParticipants;
    #[cfg(not(feature = "testonly"))]
    pub(crate) use joint::prover::ProverParticipants;
    #[cfg(feature = "testonly")]
    pub use prover::{FieldState, JointPolygeroProver};
    #[cfg(not(feature = "testonly"))]
    pub(crate) use prover::{FieldState, JointPolygeroProver};
}
cfg_verifier! {
    mod verifier;
    #[cfg(feature = "testonly")]
    pub use joint::verifier::VerifierParticipants;
    #[cfg(not(feature = "testonly"))]
    pub(crate) use joint::verifier::VerifierParticipants;
    #[cfg(feature = "testonly")]
    pub use verifier::JointPolygeroVerifier;
    #[cfg(not(feature = "testonly"))]
    pub(crate) use verifier::JointPolygeroVerifier;
}

#[cfg(test)]
mod tests;
