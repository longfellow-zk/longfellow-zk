// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's step for one `(Participant, Tail)` pair.
use sha2::Sha256;

use super::{
    super::{
        prover::{gather, respond},
        prover_commitment::encode_rows,
        FieldState, ProverParticipants,
    },
    append_values, ensure, Participant, PolygeroError,
};
use crate::{
    core::algebra::RegisteredField,
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
        random::PrivateRandom,
    },
};

impl<
        F: RuntimeField + RegisteredField + SupportsSampling,
        D: EvaluationDomain<F>,
        T: ProverParticipants,
    > ProverParticipants for (Participant<'_, F, D>, T)
{
    type States = (FieldState<F::E>, T::States);
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError> {
        ensure(w.0.len() == self.0.param.geom.nw, "witness length mismatch")?;
        self.1.validate_witnesses(&w.1)
    }
    fn validate_states(&self, w: &Self::States) -> Result<(), PolygeroError> {
        // Rows exist only from `encode`, so the geometry fixes their shape;
        // a same-shaped geometry of another parameter differs here.
        ensure(
            w.0.geom == self.0.param.geom,
            "joint prover parameter mismatch",
        )?;
        self.1.validate_states(&w.1)
    }
    fn encode(&self, w: &Self::Witnesses, rng: &mut impl PrivateRandom) -> Self::States {
        let rows = encode_rows(&self.0.param, &w.0, self.0.domain, rng, self.0.f);
        (
            FieldState {
                geom: self.0.param.geom,
                rows,
            },
            self.1.encode(&w.1, rng),
        )
    }
    fn append_encoded(&self, w: &Self::States, j: usize, h: &mut Sha256) {
        // A leaf concatenates column j from every participant in tuple order.
        // The statement fixes field widths and row counts, so no separators
        // are needed.
        append_values(self.0.f, w.0.rows.iter().map(|row| row[j].clone()), h);
        self.1.append_encoded(&w.1, j, h);
    }
    fn respond(
        &self,
        w: &Self::States,
        s: &Self::Statements,
        c: &Self::Challenges,
    ) -> Self::Bodies {
        (
            respond(
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
    fn gather(&self, w: &Self::States, b: &mut Self::Bodies, indices: &[usize]) {
        gather(&w.0.rows, &mut b.0, indices);
        self.1.gather(&w.1, &mut b.1, indices);
    }
}
