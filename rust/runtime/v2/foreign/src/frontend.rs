// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The foreign-capable frontend: a masked layered sumcheck whose values may be
//! stored outside its own field's commitment.
//!
//! The value vector is `[private inputs | sumcheck pads]`. The reduction batches
//! every layer equation and the final input equation into one linear claim
//! over that vector. The storage layer must authenticate the complete returned
//! claim; checking only the terminal input claim is insufficient.
use super::batching;
pub use super::batching::LinearClaim;
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            sumcheck::{self, SumcheckProof, TranscriptSumcheck},
            transcript::TranscriptRef,
        },
    },
};

cfg_prover! { #[path="frontend_prover.rs"] mod prover; pub use prover::{prepare, prove, Prepared}; }
cfg_verifier! { #[path="frontend_verifier.rs"] mod verifier; pub use verifier::reduce; }

/// Number of values in the frontend's value vector for `circuit`.
pub fn value_count<F: SerializableField>(circuit: &Circuit<F>) -> Result<usize, String> {
    let private = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("public prefix")?;
    private
        .checked_add(sumcheck::circuit_geometry(&[circuit])?.pad_count()?)
        .ok_or("frontend value count overflow".into())
}

#[cfg(test)]
#[path = "../tests/frontend.rs"]
mod tests;
