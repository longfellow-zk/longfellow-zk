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

//! Longfellow v2 sumcheck produces constraints on committed circuit inputs and pads.
//!
//! `prover` sends masked messages while reducing claims from circuit outputs to
//! inputs. `reduction` reconstructs the public challenges and input weights from
//! those messages. Both use `symbolic` to form the same sparse pad constraints,
//! with dense weights for the final input claim. The ZK v2 constraint compiler
//! maps the logical inputs and pads to committed positions for Polygero.
//!
//! `eval` and `dense` handle witness evaluation and binding for the prover.
//! `quad`, `monomial`, and `transcript` supply the tensor bindings, monomial weights,
//! and challenge rules shared by both roles. `verifier` evaluates the constraints
//! with revealed inputs and pads for diagnostics; production verification is
//! performed by [`crate::runtime::zk_v2::ZkVerifier`].

#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod monomial;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod quad;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod split;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod symbolic;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;

pub use proof::{LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry};
#[cfg(test)]
pub(crate) use symbolic::LayerChallenges;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use transcript::TranscriptSumcheck;

#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::core::proto::sane_logw;
use crate::runtime::proto::sumcheck_v2 as proof;

cfg_prover! {
    #[cfg(feature = "experimental")]
    pub mod boolean;
    mod dense;
    mod eval;
    mod prover;

    pub(crate) use eval::eval_circuit;
    pub use dense::bind;
    pub(crate) use prover::{prove_core, sample_pads};
}

#[cfg(test)]
pub(crate) use prover::prove;

cfg_verifier! {
    mod reduction;
    pub(crate) use reduction::derive_constraints;

    pub mod verifier;
}

#[cfg(test)]
#[path = "../tests/all/mod.rs"]
mod tests;
