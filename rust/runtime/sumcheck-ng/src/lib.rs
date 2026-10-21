// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Single-hand sumcheck, independent of the legacy runtime-sumcheck protocol.
pub mod dense;
pub mod eq;
pub mod eval;
pub mod pad;
pub mod poly;
pub mod verifier_data;
pub mod wiring;
pub use runtime_proto::sumcheck_ng as proof;
pub mod prover;
pub mod symbolic;
pub mod transcript;
pub mod verifier;

pub use dense::{as_scalar, bind};
pub use eval::{eval_circuit, EvaluatedLayer};
pub use poly::{LagrangeBasis, Poly, QuadRoundPoly, QuadWirePoly};
pub use proof::{sane_logw, LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry, MAX_LOGW};
pub use prover::{prove, prove_core};
pub use runtime_random::{RandomEngine, Transcript};
pub use transcript::TranscriptSumcheck;
pub use verifier::{derive_verifier_data, verify, verify_core};
pub use verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData};
