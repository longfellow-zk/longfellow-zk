// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Internal trace-zero reduction for ZK. The source claim is reconstructed
//! from the preceding sumcheck on the same transcript, never supplied as an
//! independent statement. Both returned equations require backend authentication.
pub(in crate::runtime::v2) mod generic;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
cfg_prover! { pub(in crate::runtime::v2) mod prover; }
cfg_verifier! { pub(in crate::runtime::v2) mod verifier; }

#[cfg(test)]
mod tests;
