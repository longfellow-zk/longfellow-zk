// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Foreign storage: one field's frontend values stored as bits in the binary
//! commitment, beside packing as a way of storing frontend inputs.
//!
//! Frontends emit affine claims over their inputs and pads without knowing
//! where those values live. Storage reductions discharge the claims: native
//! cells by Polygero rows, packed binary bits by the packing reduction, and
//! foreign bit groups by the exponent-tree adapter (`adapter`).
//!
//! - `frontend`: masked layered sumcheck batched to one claim over its values.
//! - `storage`: storage maps, typed bit groups and the reserved suffix.
//! - `mixed`: claims over native and foreign values, split by `eta` and `mu`.
//! - `adapter`: the fixed product-tree fragment and the P-256 encoder.
//! - `word`: quotient words, their pads and the masked words in proofs.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod adapter;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod batching;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod frontend;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod mixed;
pub mod storage;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod transcript;
pub mod word;

#[cfg(test)]
#[path = "../tests/foreign.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/p256.rs"]
mod tests_p256;
