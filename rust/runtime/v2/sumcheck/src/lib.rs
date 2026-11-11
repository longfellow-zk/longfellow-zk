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
//! `prover` sends masked messages while reducing an ordered set of same-field
//! circuits from outputs to inputs. `fragments` aligns their input depths and
//! supplies shared weight updates; the single-circuit case uses that same path.
//! Layers have independent quadratic, linear and constant streams. `verifier`
//! reconstructs the public challenges and input weights from
//! those messages. Both use `symbolic` to form the same sparse pad constraints,
//! with dense weights for the final input claim. The ZK v2 constraint compiler
//! maps the logical inputs and pads to committed positions for Polygero.
//!
//! `eval` and `dense` handle witness evaluation and binding for the prover.
//! `quad`, `monomial`, and `transcript` supply the tensor bindings, monomial weights,
//! and challenge rules shared by both roles. Revealed-input diagnostics live in
//! tests; complete verification is performed by [`crate::runtime::v2::zk::ZkVerifier`].

#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod circuit;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod fragments;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use fragments::geometry as circuit_geometry;
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
use crate::runtime::v2::proto::sumcheck as proof;

cfg_prover! {
    mod dense;
    mod eval;
    mod prover;

    #[cfg(test)]
    pub(crate) use eval::eval_circuit;
    pub use dense::bind;
    pub(crate) use prover::{evaluate_and_prove_circuits, sample_pads};
    #[cfg(test)]
    pub(crate) use prover::evaluate_and_prove;
}

#[cfg(test)]
pub(crate) use prover::prove;
#[cfg(test)]
pub(crate) use prover::prove_core;

cfg_verifier! {
    mod verifier;
    pub(crate) use verifier::{derive_constraints, derive_constraints_for_circuits};
}

#[cfg(test)]
#[path = "../tests/all/mod.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/diagnostic.rs"]
mod diagnostic;
