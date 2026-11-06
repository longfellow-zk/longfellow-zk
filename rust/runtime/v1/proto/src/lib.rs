// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 proof declarations and their unchanged wire encoding.

pub mod ligero;
pub mod subfield;
pub mod sumcheck;
pub mod zk;
pub use crate::runtime::proto::{merkle, util, Digest, MerkleNonce, MerkleProof};

#[cfg(test)]
#[path = "../tests/proto.rs"]
mod tests;
