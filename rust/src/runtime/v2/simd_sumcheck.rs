// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One packed-cell commitment authenticates masked sumcheck over 128 Boolean lanes.
use crate::runtime::{
    algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    v2::{
        proto::sumcheck::{LayerProof, RoundPoly},
        transcript::TranscriptRef,
    },
};
mod types;
pub(crate) use types::NativeRow;
use types::{rounds, Challenges, Product, Proof, MASKS};
mod adapter;
cfg_prover! {use types::prover::Reduction;#[cfg(feature="mldsa")]pub(crate) use prover::SharedState;}
cfg_prover! {mod packed;mod prover;}
cfg_verifier! {mod verifier;}
mod program;
pub use program::{AffineInput, Program};
mod views;
pub use views::{BitAffineInput, BitPermutation, MappedTerm};
mod shake;
mod shake_rounds;
#[cfg(feature = "mldsa")]
pub(crate) mod shared;
mod transcript;
pub use shake::SharedShake;
pub use shake_rounds::SharedShakeRounds;
#[cfg(test)]
mod tests;
