// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Tuple traversal: a `(Participant, Tail)` pair runs its field's step, then the tail's.
use sha2::{Digest as _, Sha256};

use super::{
    constraints, ensure,
    joint::{FieldChallenges, LinearStatement, Participant},
    transcript, PolygeroError,
};
use crate::{
    core::algebra::{RegisteredField, SerializableField},
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            polygero::Participants,
            proto::polygero::{FieldProof, PolygeroConfig},
            transcript::{Reading, TranscriptRef},
        },
    },
};

cfg_prover! {
    mod prover;
}
cfg_verifier! {
    mod verifier;
}

fn append_values<F: SerializableField>(
    f: &F,
    values: impl IntoIterator<Item = F::E>,
    h: &mut Sha256,
) {
    let mut buf = vec![0; f.serialized_size_bytes()];
    for x in values {
        f.to_bytes_into(&x, &mut buf);
        h.update(&buf);
    }
}
impl<
        F: RuntimeField + RegisteredField + SupportsSampling,
        D: EvaluationDomain<F>,
        T: Participants,
    > Participants for (Participant<'_, F, D>, T)
{
    type Witnesses = (Vec<F::E>, T::Witnesses);
    type Statements = (LinearStatement<F::E>, T::Statements);
    type Bodies = (FieldProof<F::E>, T::Bodies);
    type Challenges = (FieldChallenges<F::E>, T::Challenges);
    fn describe(&self, config: &mut Option<PolygeroConfig>) -> Result<usize, PolygeroError> {
        let c = self.0.param.geom.config();
        // One query index addresses a column in every field. The common profile
        // fixes that index range and response sizes; witness row counts may differ.
        ensure(config.is_none_or(|old| old == c), "joint geometry mismatch")?;
        *config = Some(c);
        Ok(1 + self.1.describe(config)?)
    }
    fn validate_statements(&self, s: &Self::Statements) -> Result<(), PolygeroError> {
        constraints::validate(self.0.param.geom.nw, s.0.b.len(), &s.0.a)?;
        self.1.validate_statements(&s.1)
    }
    fn challenges(&self, s: &Self::Statements, t: &mut Reading<'_>) -> Self::Challenges {
        (
            transcript::challenges(t, &self.0.param, s.0.b.len(), self.0.f),
            self.1.challenges(&s.1, t),
        )
    }
    fn send_responses(&self, b: &Self::Bodies, t: &mut TranscriptRef<'_>) {
        transcript::send_response(t, &b.0, self.0.f);
        self.1.send_responses(&b.1, t);
    }
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError> {
        b.0.validate(&self.0.param.geom)?;
        self.1.validate_bodies(&b.1)
    }
    #[cfg(any(test, feature = "testonly"))]
    fn wire_len(&self) -> Option<usize> {
        let [response, rows] =
            FieldProof::<()>::wire_lengths(&self.0.param.geom, self.0.f.serialized_size_bytes())?;
        response.checked_add(rows)?.checked_add(self.1.wire_len()?)
    }
    #[cfg(any(test, feature = "testonly"))]
    fn write_responses(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError> {
        b.0.write_response(out, &self.0.param.geom, self.0.f)?;
        self.1.write_responses(&b.1, out)
    }
    #[cfg(any(test, feature = "testonly"))]
    fn write_rows(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError> {
        b.0.write_rows(out, &self.0.param.geom, self.0.f)?;
        self.1.write_rows(&b.1, out)
    }
    #[cfg(any(test, feature = "testonly"))]
    fn read_responses(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError> {
        Ok((
            FieldProof::read_response(bytes, &self.0.param.geom, self.0.f)?,
            self.1.read_responses(bytes)?,
        ))
    }
    #[cfg(any(test, feature = "testonly"))]
    fn read_rows(&self, b: &mut Self::Bodies, bytes: &mut &[u8]) -> Result<(), PolygeroError> {
        b.0.read_rows(bytes, &self.0.param.geom, self.0.f)?;
        self.1.read_rows(&mut b.1, bytes)
    }
}
