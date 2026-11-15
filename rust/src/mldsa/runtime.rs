// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public-key ML-DSA over the foreign storage layer.
//!
//! One packed binary commitment holds the signature witness. The public-key
//! arithmetic modulo q is linear in that witness: six uniform row projections
//! form one claim over F_q^6 whose terms are binary words, proven by the
//! exact-mode adapter. No other field commits anything; there is no prime
//! frontend. The driver is this module's `prove` and `verify`: commitment,
//! projection challenge, adapter rounds, the binary frontend with the adapter's
//! fixed fragment, then the joint opening.
use crate::{
    mldsa::{
        proto::{MlDsaParams, N},
        runtime::reference::PublicKey,
    },
    runtime::{
        algebra::{fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field as BF},
        v2::foreign::adapter::{exact::ExactClaims, AdapterMode},
    },
};
mod binary;
pub(crate) mod projection;
mod proto;
pub mod reference;
mod transcript;
cfg_prover! {mod prover;mod witness;pub use prover::prove;}
cfg_verifier! {mod verifier;pub use verifier::verify;}
pub mod hidden;

mod model;
pub use model::Circuits;
use model::{public_key, Link, QB};

mod source;
pub use source::KeccakSource;

mod packed;
