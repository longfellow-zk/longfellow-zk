// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's operations on a participant list.
use sha2::Sha256;

use super::{Participants, PolygeroError};
use crate::runtime::random::PrivateRandom;

/// The prover's passes over a participant list: it checks and encodes the
/// witnesses, hashes the encoded columns, then forms every field's response
/// and gathers the opened columns.
pub trait ProverParticipants: Participants {
    /// The prover's encoded rows between commitment and opening.
    type States;
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError>;
    /// Check that every field's rows were encoded for this list's geometry.
    fn validate_states(&self, w: &Self::States) -> Result<(), PolygeroError>;
    fn encode(&self, w: Self::Witnesses, rng: &mut impl PrivateRandom) -> Self::States;
    fn append_encoded(&self, w: &Self::States, j: usize, h: &mut Sha256);
    fn respond(&self, w: &Self::States, s: &Self::Statements, c: &Self::Challenges)
        -> Self::Bodies;
    fn gather(&self, w: &Self::States, b: &mut Self::Bodies, indices: &[usize]);
}
impl ProverParticipants for () {
    type States = ();
    fn validate_witnesses(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn validate_states(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn encode(&self, _: (), _: &mut impl PrivateRandom) {}
    fn append_encoded(&self, _: &(), _: usize, _: &mut Sha256) {}
    fn respond(&self, _: &(), _: &(), _: &()) {}
    fn gather(&self, _: &(), _: &mut (), _: &[usize]) {}
}
