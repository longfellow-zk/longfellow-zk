// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Experimental parser-free mdoc proof with one binary-field commitment.
//!
//! Use `development_provider::compile_next` for its trusted fixed-slot bundle.
//! The hash predicate checks byte offsets without structural CBOR witnesses.
//!
//! The signature frontend's private inputs and sumcheck pads are bit groups
//! in the binary witness. Both frontends retain their original arithmetic;
//! a P-256 exponent-tree adapter authenticates the prime frontend's batched
//! claim against the sole binary commitment.
mod encoding;
pub use encoding::SignatureEncoding;
mod constants;
mod geometry;
mod link;
mod proof;
mod transcript;
pub use geometry::{proof_geometry, proof_geometry_with_encoding};
pub use proof::ProofGeometry;
cfg_prover! {
    mod prover;
    pub use prover::{run_mdoc_prover, run_mdoc_prover_inner, run_mdoc_prover_inner_with_encoding};
}
cfg_verifier! {
    mod verifier;
    pub use verifier::{run_mdoc_verifier, run_mdoc_verifier_with_encoding};
}
#[cfg(test)]
mod tests;
