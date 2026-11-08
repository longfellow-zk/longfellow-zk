// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1 proof declarations and their unchanged wire encoding.

pub mod ligero;
pub mod merkle;
pub mod subfield;
pub mod sumcheck;
pub mod util;
pub mod zk;
pub use merkle::{Digest, MerkleNonce, MerkleProof, DIGEST_LEN, NONCE_LEN};

#[cfg(test)]
#[path = "../tests/proto.rs"]
mod tests;
