// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's operations on a participant list.
use sha2::Sha256;

use super::{Participants, PolygeroError};

/// The verifier's passes over a participant list: it checks the bodies'
/// shapes, hashes the opened columns, then checks every field's response.
#[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
pub trait VerifierParticipants: Participants {
    /// Check that every field's response and rows have its geometry's shape.
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError>;
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
    fn validate_bodies(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn append_opened(&self, _: &(), _: usize, _: usize, _: &mut Sha256) {}
    fn check(&self, _: &(), _: &(), _: &(), _: &[usize]) -> Result<(), PolygeroError> {
        Ok(())
    }
}
