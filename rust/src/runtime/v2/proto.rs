// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof declarations, geometry and canonical complete-proof encoding.

pub mod composed;
pub mod dual_packing;
mod merkle;
pub mod polygero;
pub mod sumcheck;
pub mod tags;
pub(crate) mod util;
pub mod witness_selection;
pub mod zk;
pub(in crate::runtime::v2) use merkle::MerkleProof;
pub use merkle::{Digest, NONCE_LEN};
cfg_role! {
    mod field;
    pub(crate) use field::{read_bytes_32, read_field};
    pub(in crate::runtime::v2) use merkle::MerkleNonce;
}

#[cfg(test)]
pub(crate) mod tests;
