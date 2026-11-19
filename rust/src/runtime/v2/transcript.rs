// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! SHA-256 strands, the one message encoding, typed transcript sessions, and
//! complete-proof seals.

#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod bound;
#[cfg(test)]
pub(crate) mod cheat;
mod message;
#[cfg(any(test, feature = "prover"))]
mod prover;

mod session;
mod strand;
#[cfg(test)]
mod trace;
mod verifier;

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use bound::{Bound, Opened};
#[cfg(test)]
pub(crate) use message::REGISTERED_FIELDS;
pub use message::{Encoder, Message, ProverMessage, SetupMessage, ZkStatement, ZK_PROTOCOL_ID};
#[cfg(any(test, feature = "prover"))]
pub use prover::EncodedProof;
// Outside the crate a bare session exists only in tests and benchmarks
// (`Transcript::for_test`); elsewhere every session is an `Opened`'s.
#[cfg(not(feature = "testonly"))]
pub(crate) use session::Transcript;
#[cfg(feature = "testonly")]
pub use session::Transcript;
pub use session::{Header, Statement, TranscriptRef, SEAL_BYTES};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use session::{Reading, SessionStamp};
pub use strand::{Prf, Strand};
#[cfg(test)]
pub(crate) use trace::{Event, TestMessage, Trace};
pub use verifier::{Unverified, VerifiedProof};
