// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 proof declarations and their unchanged wire encoding.

pub mod ligero_v1;
pub mod subfield_v1;
pub mod sumcheck_v1;
pub mod zk_v1;
pub use crate::runtime::proto::{merkle, util, Digest, MerkleNonce, MerkleProof};

#[cfg(test)]
#[path = "../tests/proto_v1.rs"]
mod tests;
