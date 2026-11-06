// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trace-zero packing reductions. Both returned linear equations must be
//! authenticated against the original commitment to words, auxiliaries and masks.
pub mod generic;
mod generic_codec;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
pub const PACKING_BASIS_ID: u32 = 2;
cfg_prover! { pub mod prover; }
cfg_verifier! { pub mod verifier; }

#[cfg(test)]
#[path = "../tests/generic.rs"]
mod tests;
