// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Hidden-key ML-DSA over the foreign storage layer.
//!
//! With a private key, A*z and c*t1 multiply private values, so a native
//! sextic-extension sumcheck checks them. That frontend has pure foreign
//! coordinate storage: its inputs (base-field words) and its pads (all six
//! coordinates) are bit groups in the binary commitment, and it commits
//! nothing of its own. Its batched claim, expanded by coordinate, is one claim
//! over F_q^6 for the exact-mode adapter. Authorization of the key and binding
//! mu to a message remain application predicates.
//!
//! The driver is this module's `prove` and `verify`. On one transcript:
//!
//! 1. the layout bindings, then the commitment of the binary host alone;
//! 2. the native frontend's sumcheck and its batched claim;
//! 3. the adapter's masked quotients, which define the fragment's leaves;
//! 4. the permutation points gamma, then the host's sumcheck over the binary relation and the
//!    adapter fragment (scalar or SIMD SHAKE packing);
//! 5. the joint opening of the host's statement.
mod layout;
pub use layout::Circuits;

use crate::runtime::{
    algebra::{gf2_128::Gf2_128Field, range_interpolation::CrtInterpolatorFactory},
    v2::foreign::adapter::AdapterMode,
};
mod proto;
mod transcript;
cfg_prover! {mod witness;mod prover;pub use prover::prove;}
cfg_verifier! {mod verifier;pub use verifier::verify;}

mod model;
use model::{basis, Link, HQ};
