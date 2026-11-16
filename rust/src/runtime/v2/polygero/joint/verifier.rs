// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's operations on a participant list.
use sha2::Sha256;

use super::{Participants, PolygeroError};

/// The verifier's passes over a participant list: it hashes the opened
/// columns, then checks every field's response.
pub trait VerifierParticipants: Participants {
    fn append_opened(&self, w: &Self::Bodies, q: usize, t: usize, h: &mut Sha256);
    fn check(
        &self,
        b: &Self::Bodies,
        s: &Self::Statements,
        c: &Self::Challenges,
        indices: &[usize],
    ) -> Result<(), PolygeroError>;
}
impl VerifierParticipants for () {
    fn append_opened(&self, _: &(), _: usize, _: usize, _: &mut Sha256) {}
    fn check(&self, _: &(), _: &(), _: &(), _: &[usize]) -> Result<(), PolygeroError> {
        Ok(())
    }
}
