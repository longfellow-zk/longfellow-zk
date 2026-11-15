// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Tuple traversal: a `(Participant, Tail)` pair runs its field's step, then the tail's.
use sha2::{Digest as _, Sha256};

#[cfg(any(test, feature = "prover"))]
use super::FieldState;
use super::{
    constraints, ensure,
    joint::{FieldChallenges, LinearStatement, Participant},
    transcript, PolygeroError,
};
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::PrivateRandom;
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
        const W: usize,
        F: RuntimeField<W> + RegisteredField + SupportsSampling,
        D: EvaluationDomain<W, F>,
        T: Participants,
    > Participants for (Participant<'_, W, F, D>, T)
{
    type Witnesses = (Vec<F::E>, T::Witnesses);
    type Statements = (LinearStatement<F::E>, T::Statements);
    #[cfg(any(test, feature = "prover"))]
    type States = (FieldState<F::E>, T::States);
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
    fn equations(&self, s: &Self::Statements, out: &mut Vec<usize>) {
        out.push(s.0.b.len());
        self.1.equations(&s.1, out);
    }
    fn challenges(&self, counts: &[usize], t: &mut Reading<'_>) -> Self::Challenges {
        // A missing count draws nothing for the field; the shape check
        // rejects the result.
        let (&n, rest) = counts.split_first().unwrap_or((&0, &[]));
        (
            transcript::challenges(t, &self.0.param, n, self.0.f),
            self.1.challenges(rest, t),
        )
    }
    fn validate_challenges(
        &self,
        s: &Self::Statements,
        c: &Self::Challenges,
    ) -> Result<(), PolygeroError> {
        let param = &self.0.param;
        let samples = param.geom.s + 1;
        ensure(
            c.0.alpha.len() == s.0.b.len()
                && c.0.batching_samples.len() == param.batched_rows().len()
                && c.0.batching_samples.iter().all(|b| b.len() == samples),
            "batching weights do not fit the statement",
        )?;
        self.1.validate_challenges(&s.1, &c.1)
    }
    fn send_responses(&self, b: &Self::Bodies, t: &mut TranscriptRef<'_>) {
        transcript::send_response(t, &b.0, self.0.f);
        self.1.send_responses(&b.1, t);
    }
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError> {
        b.0.validate(&self.0.param.geom)?;
        self.1.validate_bodies(&b.1)
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn wire_len(&self) -> Option<usize> {
        let [response, rows] =
            FieldProof::<()>::wire_lengths(&self.0.param.geom, self.0.f.serialized_size_bytes())?;
        response.checked_add(rows)?.checked_add(self.1.wire_len()?)
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_responses(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError> {
        b.0.write_response(out, &self.0.param.geom, self.0.f)?;
        self.1.write_responses(&b.1, out)
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_rows(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError> {
        b.0.write_rows(out, &self.0.param.geom, self.0.f)?;
        self.1.write_rows(&b.1, out)
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_responses(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError> {
        Ok((
            FieldProof::read_response(bytes, &self.0.param.geom, self.0.f)?,
            self.1.read_responses(bytes)?,
        ))
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_rows(&self, b: &mut Self::Bodies, bytes: &mut &[u8]) -> Result<(), PolygeroError> {
        b.0.read_rows(bytes, &self.0.param.geom, self.0.f)?;
        self.1.read_rows(&mut b.1, bytes)
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError> {
        ensure(w.0.len() == self.0.param.geom.nw, "witness length mismatch")?;
        self.1.validate_witnesses(&w.1)
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_states(&self, w: &Self::States) -> Result<(), PolygeroError> {
        // Rows exist only from `encode`, so the geometry fixes their shape;
        // a same-shaped geometry of another parameter differs here.
        ensure(
            w.0.geom == self.0.param.geom,
            "joint prover parameter mismatch",
        )?;
        self.1.validate_states(&w.1)
    }
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, w: Self::Witnesses, rng: &mut impl PrivateRandom) -> Self::States {
        let rows =
            super::prover_commitment::encode_rows(&self.0.param, w.0, self.0.domain, rng, self.0.f);
        (
            FieldState {
                geom: self.0.param.geom,
                rows,
            },
            self.1.encode(w.1, rng),
        )
    }
    #[cfg(any(test, feature = "prover"))]
    fn append_encoded(&self, w: &Self::States, j: usize, h: &mut Sha256) {
        // A leaf concatenates column j from every participant in tuple order.
        // The statement fixes field widths and row counts, so no separators
        // are needed.
        append_values(self.0.f, w.0.rows.iter().map(|row| row[j].clone()), h);
        self.1.append_encoded(&w.1, j, h);
    }
    #[cfg(any(test, feature = "prover"))]
    fn respond(
        &self,
        w: &Self::States,
        s: &Self::Statements,
        c: &Self::Challenges,
    ) -> Self::Bodies {
        (
            super::prover::respond(
                &self.0.param,
                &w.0.rows,
                &s.0,
                &c.0,
                self.0.domain,
                self.0.f,
            ),
            self.1.respond(&w.1, &s.1, &c.1),
        )
    }
    #[cfg(any(test, feature = "prover"))]
    fn gather(&self, w: &Self::States, b: &mut Self::Bodies, indices: &[usize]) {
        super::prover::gather(&w.0.rows, &mut b.0, indices);
        self.1.gather(&w.1, &mut b.1, indices);
    }
    #[cfg(any(test, feature = "verifier"))]
    fn append_opened(&self, w: &Self::Bodies, q: usize, t: usize, h: &mut Sha256) {
        // Proof rows store t values in query order. Here q is the position in
        // that order, whereas append_encoded receives the actual column index.
        append_values(
            self.0.f,
            w.0.rows.chunks_exact(t).map(|row| row[q].clone()),
            h,
        );
        self.1.append_opened(&w.1, q, t, h);
    }
    #[cfg(any(test, feature = "verifier"))]
    fn check(
        &self,
        b: &Self::Bodies,
        s: &Self::Statements,
        c: &Self::Challenges,
        indices: &[usize],
    ) -> Result<(), PolygeroError> {
        super::verifier::check_response(
            &self.0.param,
            &b.0,
            &s.0,
            &c.0,
            indices,
            self.0.domain,
            self.0.f,
        )?;
        self.1.check(&b.1, &s.1, &c.1, indices)
    }
}
