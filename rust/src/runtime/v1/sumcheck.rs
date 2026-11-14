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

//! Longfellow v1's two-hand sumcheck over multilinear witness evaluations.
//!
//! Each circuit layer carries two claims. The next layer combines them with
//! alpha, binds the output index of QUAD, then alternates right- and left-hand
//! rounds. Each round binds one Boolean coordinate by (1-z)*even+z*odd and sends
//! masked evaluations at the first and third interpolation points.
//!
//! `prover` produces messages and local verifier data; `verifier` reconstructs
//! that data from the transcript. `symbolic` turns it into constraints on hidden
//! inputs and pads, which `zk` compiles for Ligero. `dense`, `eq`, and `hquad`
//! implement the dense witness and sparse tensor bindings. The public module
//! and wire interfaces retain the legacy conventions used by circuits through v7.
mod dense;
mod eq;
pub mod eval;
mod hquad;
pub mod pad;
mod poly;
mod round_data;
pub mod symbolic;
mod transcript;

pub use dense::{as_scalar, bind, bind_all, normalize};
pub use eq::eq;
pub use hquad::HQuad;
pub use poly::{QuadRoundPoly, QuadWirePoly};
pub use round_data::{LayerVerifierData, RoundCoefficients, VerifierData};
pub use transcript::TranscriptSumcheck;

cfg_prover! {
    mod prover;
    pub use prover::{prove, prove_core};
}

cfg_verifier! {
    mod verifier;
    pub use verifier::{derive_verifier_data, verify, verify_core};
}

#[cfg(test)]
mod tests;
