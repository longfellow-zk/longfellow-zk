// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked prime-field sumcheck without a field-specific commitment backend.
//!
//! This reduction batches every layer equation and the final input equation.
//! Its caller must authenticate the complete returned claim against the same
//! committed witness. Checking only the terminal input claim is insufficient.
mod row_batching;
pub(crate) use row_batching::LinearClaim;

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

cfg_prover! { mod prover; pub(crate) use prover::{prepare, prove, Prepared}; }
cfg_verifier! { mod verifier; pub(crate) use verifier::reduce; }

#[cfg(test)]
#[path = "../../../../tests/v2_masked_prime.rs"]
mod tests;
