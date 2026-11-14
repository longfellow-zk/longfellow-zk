// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! SHA-256 strands, typed transcript rounds, and complete-proof final seals.

mod prover;

mod session;
mod strand;
mod verifier;

pub use prover::EncodedProof;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use session::{Reading, RoundEnd};
pub use session::{Transcript, TranscriptRef, Writing};
pub use strand::{Prf, Strand};
pub use verifier::{Unverified, VerifiedProof};
