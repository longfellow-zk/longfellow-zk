// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The selected-witness protocol, using explicit transcript rounds, packing,
//! layered sumcheck and one joint Polygero commitment.
//!
//! Packing reductions are internal to ZK; their source coefficients come from
//! the preceding sumcheck on the same transcript.
//! ```compile_fail
//! use longfellow_zk::runtime::v2::dual_packing::verifier::reduce;
//! ```
//! V2 authentication is internal to its proof protocols.
//! ```compile_fail
//! use longfellow_zk::runtime::v2::merkle::MerkleHeap;
//! ```
//! ```compile_fail
//! use longfellow_zk::runtime::v2::proto::MerkleProof;
//! ```
//! V1 and v2 digests are distinct protocol types.
//! ```compile_fail
//! let old = longfellow_zk::runtime::v1::proto::Digest::default();
//! let _: longfellow_zk::runtime::v2::proto::Digest = old;
//! ```

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod dual_packing;

pub mod foreign;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) mod merkle;

pub mod polygero;

pub mod proto;

pub mod sumcheck;

pub mod transcript;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod witness_selection;

pub mod zk;
