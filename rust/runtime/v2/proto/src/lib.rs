// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof declarations, geometry and canonical complete-proof encoding.

pub mod dual_packing;
mod field;
pub mod polygero;
pub mod sumcheck;
pub mod witness_selection;
pub mod zk;
pub(crate) use field::read_field;

pub use crate::runtime::proto::{merkle, util, Digest, MerkleNonce, MerkleProof};

#[cfg(test)]
#[path = "../tests/fixtures.rs"]
mod fixtures;

#[cfg(test)]
#[path = "../tests/proto.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/polygero.rs"]
mod tests_polygero;
