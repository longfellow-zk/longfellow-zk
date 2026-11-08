// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof declarations, geometry and canonical complete-proof encoding.

pub mod dual_packing;
mod field;
mod merkle;
pub mod polygero;
pub mod sumcheck;
pub(crate) mod util;
pub mod witness_selection;
pub mod zk;
pub(crate) use field::read_field;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(in crate::runtime::v2) use merkle::MerkleNonce;
pub(in crate::runtime::v2) use merkle::MerkleProof;
pub use merkle::{Digest, NONCE_LEN};

#[cfg(test)]
#[path = "../tests/fixtures.rs"]
mod fixtures;

#[cfg(test)]
#[path = "../tests/proto.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/polygero.rs"]
mod tests_polygero;
#[cfg(test)]
#[path = "../tests/readers.rs"]
mod tests_readers;
