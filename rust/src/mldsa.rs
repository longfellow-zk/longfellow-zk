// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! ML-DSA signature relations and zero-knowledge proof applications.
pub mod proto;
cfg_compiler! { pub mod compile; }
#[cfg(all(
    feature = "compiler",
    any(test, feature = "prover", feature = "verifier")
))]
pub mod development_provider;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub mod runtime;

cfg_testonly! { pub mod testcases; }
