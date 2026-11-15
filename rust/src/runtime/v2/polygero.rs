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
//! No statement is absorbed: the batching weights (`BatchWeights`) follow the
//! last message every statement is derived from, drawn by the caller as a
//! `Challenge` input (transcript I8) that `prove` and `verify` accept, and
//! every H/Z response is absorbed before a single ordered set of column
//! queries is drawn.
//! A one-field invocation uses `(participant, ())` through the same API.
//!
//! `prover` and `verifier` own their field equations; `prover_commitment` encodes masked
//! rows, `joint` coordinates tuples, `participant` traverses them, and `transcript`
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
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod constraints;
mod error;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use error::ensure;
pub use error::PolygeroError;

#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::v2::merkle::hash;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod joint;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod param;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod participant;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod polynomials;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub use config::PolygeroLinearTerm;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use param::PolygeroParam;

cfg_prover! { mod prover_commitment; }
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use joint::{
    BatchWeights, FieldChallenges, JointPolygeroParam, LinearStatement, Participant, Participants,
};
cfg_prover! {mod prover; pub use prover::JointPolygeroProver;}
cfg_verifier! {mod verifier; pub use verifier::JointPolygeroVerifier;}

#[cfg(test)]
mod tests;
