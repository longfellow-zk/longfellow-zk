// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked prime-field sumcheck without a field-specific commitment backend.
//!
//! This reduction batches every layer equation and the final input equation.
//! Its caller must authenticate the complete returned claim against the same
//! committed witness. Checking only the terminal input claim is insufficient.
use super::row_batching;
pub(crate) use super::row_batching::LinearClaim;
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        random::transcript_v2::Transcript,
        sumcheck_v2::{self, SumcheckProof, SumcheckProofGeometry, TranscriptSumcheck},
    },
};

cfg_prover! { #[path="prime_prover.rs"] mod prover; pub(crate) use prover::{prepare, prove, Prepared}; }
cfg_verifier! { #[path="prime_verifier.rs"] mod verifier; pub(crate) use verifier::reduce; }
