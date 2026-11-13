// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Foreign storage: one field's frontend values stored as bits in the binary
//! commitment, beside packing as a way of storing frontend inputs.
//!
//! The zk layer owns storage maps and the split of a participant's batched
//! claim (`zk::storage`, `zk::split`). This module discharges the resulting
//! modular claims over foreign bit groups with the exponent-tree adapter.
//!
//! - `adapter`: the fixed product-tree fragment and the P-256 encoder.
//! - `word`: quotient words, their pads and the masked words in proofs.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod adapter;
pub mod word;

#[cfg(test)]
#[path = "../tests/foreign.rs"]
mod tests;

#[cfg(test)]
#[path = "../tests/p256.rs"]
mod tests_p256;
