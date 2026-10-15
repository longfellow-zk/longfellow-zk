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

//! Zero-knowledge proofs with an explicit sumcheck challenge schedule.
//!
//! Constructors default to [`SumcheckOrder::HandMajor`] (the dense, two-pass
//! prover). Select [`SumcheckOrder::RoundMajor`] on **both** peers with
//! [`ZkProver::with_sumcheck_order`] and [`ZkVerifier::with_sumcheck_order`] for
//! the legacy interleaved protocol, including its symbolic verifier.
//!
//! Hand-major accepts arbitrary LFC1/LFC2 term traversal. Round-major requires
//! the stored circuit to already be Morton-ordered by its input pairs. It binds
//! g and coalesces adjacent duplicates before sparse hand binding. Neither
//! prover sorts the circuit or its working pairs. Verification evaluates the
//! final wiring polynomial directly in either mode, without sorting.
//!
//! The original circuit, ID, segmentation, proof serialization, and proof
//! geometry are unchanged by selecting an order. Proof contents generally
//! differ, and transcript-dependent Merkle paths can change serialized length.
//! The schedule is trusted protocol configuration, not inferred from
//! the circuit layout or auto-detected from a proof.

pub(crate) mod circuit_pad;
pub mod common;
pub(crate) mod expression;
pub mod prover;
pub mod symbolic_sumcheck_verifier;
pub mod verifier;

pub use prover::ZkProver;
pub use runtime_proto::ZkProof;
pub use runtime_sumcheck::SumcheckOrder;
pub use verifier::ZkVerifier;
