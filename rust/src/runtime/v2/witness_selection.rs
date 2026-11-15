// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 masked linear fingerprints between frontend reduction and joint Polygero.
//!
//! Each field appends two fresh private masks to its original witness, commits,
//! and samples two independent full coefficient vectors. All fields sample in
//! one reading phase; all responses are bound before the caller runs sumcheck.
//! The opaque role states retain the backend handles and the commitment's
//! coefficients and responses; completing the opening (`finish`) attaches the
//! fingerprint equations to the later frontend statements before the
//! backend draws its batching weights.
//! The early responses fix targets; only the final backend check authenticates
//! them. Complete-proof sealing remains the enclosing protocol's responsibility.
use crate::{
    core::algebra::RegisteredField,
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            polygero::{Participant, PolygeroLinearTerm},
            proto::witness_selection::{FingerprintResponse, FINGERPRINTS},
            transcript::{Reading, SessionStamp, TranscriptRef},
        },
    },
};
mod fields;
mod transcript;

pub(in crate::runtime::v2) use fields::witness_count;
pub use fields::{Bodies, Field, Fields, Param, Statements, Witnesses};

impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + RegisteredField + SupportsSampling,
        D: EvaluationDomain<W, F>,
        T: Fields,
    > Fields for (Field<'a, W, F, D>, T)
{
    type Backend = (Participant<'a, W, F, D>, T::Backend);
    type Coefficients = ([Vec<F::E>; FINGERPRINTS], T::Coefficients);
    type Responses = (FingerprintResponse<F::E>, T::Responses);
    fn backend(&self) -> Self::Backend {
        (self.0.backend.clone(), self.1.backend())
    }
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients {
        (
            transcript::field_coefficients(&self.0, r),
            self.1.coefficients(r),
        )
    }
    fn send_responses(&self, responses: &Self::Responses, t: &mut TranscriptRef<'_>) {
        transcript::send_field_response(&self.0, &responses.0, t);
        self.1.send_responses(&responses.1, t);
    }
    fn authenticate(
        &self,
        mut statements: Statements<Self>,
        coefficients: Self::Coefficients,
        responses: &Self::Responses,
        session: &SessionStamp,
    ) -> Result<Statements<Self>, String> {
        let f = self.0.f;
        let n = self.0.cells;
        // A pointer comparison: the equations' stamp is the session's own.
        if statements.0.session != *session {
            return Err("frontend equations derived on another session".into());
        }
        if statements
            .0
            .a
            .iter()
            .any(|term| term.w >= n || term.c >= statements.0.b.len())
        {
            return Err("frontend constraint outside original witness layout".into());
        }
        for (j, (a, response)) in coefficients
            .0
            .into_iter()
            .zip(&responses.0.values)
            .enumerate()
        {
            if a.len() != n {
                return Err("fingerprint coefficient count".into());
            }
            let c = statements.0.b.len();
            // A*w+b=0 authenticates <a,w> + m - response = 0 in any characteristic.
            statements.0.b.push(f.neg(response));
            statements
                .0
                .a
                .extend(
                    a.into_iter()
                        .enumerate()
                        .map(|(w, k)| PolygeroLinearTerm { c, w, k }),
                );
            statements.0.a.push(PolygeroLinearTerm {
                c,
                w: n + j,
                k: f.one(),
            });
        }
        Ok((
            statements.0,
            self.1
                .authenticate(statements.1, coefficients.1, &responses.1, session)?,
        ))
    }
}

cfg_prover! { mod prover; pub use prover::{commit, Prover, ProverFields}; }
cfg_verifier! { mod verifier; pub use verifier::{Authenticated, Verifier}; }
