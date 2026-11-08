// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Internal trace-zero reduction for ZK. The source claim is reconstructed
//! from the preceding sumcheck on the same transcript, never supplied as an
//! independent statement. Both returned equations require backend authentication.
pub mod generic;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub const PACKING_BASIS_ID: u32 = 2;
cfg_prover! { pub mod prover; }
cfg_verifier! { pub mod verifier; }

#[cfg(test)]
#[path = "../tests/generic.rs"]
mod tests;
#[cfg(test)]
#[path = "../tests/transcript.rs"]
mod transcript_tests;
