// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's step for one `(Participant, Tail)` pair.
use sha2::Sha256;

use super::{
    super::{verifier::check_response, VerifierParticipants},
    append_values, Participant, PolygeroError,
};
use crate::{
    core::algebra::RegisteredField,
    runtime::algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
};

impl<
        F: RuntimeField + RegisteredField + SupportsSampling,
        D: EvaluationDomain<F>,
        T: VerifierParticipants,
    > VerifierParticipants for (Participant<'_, F, D>, T)
{
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
    fn check(
        &self,
        b: &Self::Bodies,
        s: &Self::Statements,
        c: &Self::Challenges,
        indices: &[usize],
    ) -> Result<(), PolygeroError> {
        check_response(
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
