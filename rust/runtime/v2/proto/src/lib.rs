// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof declarations, geometry and canonical complete-proof encoding.

pub mod dual_packing;
pub mod polygero;
pub mod sumcheck_v2;
pub mod witness_selection;
pub mod zk_v2;
pub use crate::runtime::proto::{merkle, util, Digest, MerkleNonce, MerkleProof};

#[cfg(test)]
#[path = "../tests/proto_v2.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/polygero.rs"]
mod tests_polygero;
