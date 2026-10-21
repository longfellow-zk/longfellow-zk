// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Zero-knowledge proofs using only the single-hand sumcheck protocol.
//! The legacy runtime-zk crate remains a separate entry point.
pub mod common;
pub mod constraint_compiler;
pub mod prover;
pub mod verifier;
pub use runtime_proto::zk_ng as proof;

pub use proof::{witness_and_constraint_count, ZkProof, ZkProofGeometry};
pub use prover::ZkProver;
pub use verifier::ZkVerifier;
