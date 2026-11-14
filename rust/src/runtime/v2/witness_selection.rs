// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 masked linear fingerprints between frontend reduction and joint Polygero.
//!
//! Each field appends two fresh private masks to its original witness, commits,
//! and samples two independent full coefficient vectors. All fields sample in
//! one reading phase; all responses are bound before the caller runs sumcheck.
//! The opaque role states retain the backend handles and automatically attach
//! the fingerprint equations when authenticating the later frontend statements.
//! The early responses fix targets; only the final backend check authenticates
//! them. Complete-proof sealing remains the enclosing protocol's responsibility.
pub use crate::runtime::v2::proto::witness_selection::{FingerprintResponse, FINGERPRINTS};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            polygero::{Participant, PolygeroLinearTerm},
            transcript::{Reading, Writing},
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
        F: RuntimeField<W> + SerializableField + SupportsSampling,
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
    fn count(&self) -> usize {
        1 + self.1.count()
    }
    fn bind_layout(&self, w: &mut Writing<'_>) {
        transcript::absorb_field_layout(&self.0, w);
        self.1.bind_layout(w);
    }
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients {
        (
            transcript::field_coefficients(&self.0, r),
            self.1.coefficients(r),
        )
    }
    fn absorb_responses(&self, responses: &Self::Responses, w: &mut Writing<'_>) {
        transcript::absorb_field_responses(&self.0, &responses.0, w);
        self.1.absorb_responses(&responses.1, w);
    }
    fn authenticate(
        &self,
        mut statements: Statements<Self>,
        coefficients: Self::Coefficients,
        responses: &Self::Responses,
    ) -> Result<Statements<Self>, String> {
        let f = self.0.f;
        let n = self.0.cells;
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
                .authenticate(statements.1, coefficients.1, &responses.1)?,
        ))
    }
}

cfg_prover! { mod prover; pub use prover::{commit, Prover, ProverFields}; }
cfg_verifier! { mod verifier; pub use verifier::{Authenticated, Verifier}; }
