// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof declarations, geometry and canonical complete-proof encoding.

pub mod composed;
pub mod dual_packing;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod field;
mod merkle;
pub mod polygero;
pub mod sumcheck;
pub mod tags;
pub(crate) mod util;
pub mod witness_selection;
pub mod zk;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) use field::read_field;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(in crate::runtime::v2) use merkle::MerkleNonce;
pub(in crate::runtime::v2) use merkle::MerkleProof;
pub use merkle::{Digest, NONCE_LEN};

#[cfg(test)]
pub(crate) mod tests;
