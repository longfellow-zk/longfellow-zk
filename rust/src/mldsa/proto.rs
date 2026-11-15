// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared ML-DSA parameters and trusted circuit-archive metadata.
mod params;
pub use params::{MlDsa44, MlDsa65, MlDsaParams, D, N, REJ_NTT_BYTES, SAMPLE_IN_BALL_BYTES, ZETAS};
mod adapter;
pub use adapter::{public_widths, CLAIMS, HIDDEN_QUOTIENT_BITS, PUBLIC_QUOTIENT_BITS};
mod shake_layout;
pub use shake_layout::{BinaryKeccak, KeccakBackend};
pub(crate) use shake_layout::{KECCAK_ROUNDS, SHAKE256_RATE};
cfg_compiler! { pub(crate) use shake_layout::STATE_ROUNDS; }
cfg_prover_or_compiler! {
    mod hidden;
    pub(crate) use hidden::shared_widths;
}

/// One stored base coordinate of a native value.
// Compiler-only builds write this shared metadata; runtime roles read it.
#[cfg_attr(
    not(any(test, feature = "prover", feature = "verifier")),
    allow(dead_code)
)]
#[derive(Clone)]
pub(crate) struct Source {
    pub value: usize,
    pub coordinate: usize,
    pub width: usize,
}
/// Trusted compiler output. Loading derives runtime-only pads and SIMD layouts.
#[cfg_attr(
    not(any(test, feature = "prover", feature = "verifier")),
    allow(dead_code)
)]
pub struct HiddenArchive {
    pub binary: Vec<u8>,
    pub arithmetic: Vec<u8>,
    pub keccak: BinaryKeccak,
    pub(crate) sources: Vec<Source>,
    pub(crate) positions: Vec<usize>,
    pub(crate) links: Vec<(Vec<usize>, Vec<usize>)>,
    pub(crate) base_private: usize,
    pub(crate) key_start: usize,
}

mod sample_routing;
pub(crate) use sample_routing::{routing_plan, RoutingPlan, ROUTING_SIZE};
