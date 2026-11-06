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
        proto::Digest,
        v2::{
            polygero::{
                joint::Participants as BackendParticipants, JointPolygeroParam, Participant,
                PolygeroLinearTerm, PolygeroParam,
            },
            proto::polygero::PolygeroConfig,
            transcript::{Reading, Writing},
        },
    },
};
mod transcript;

pub type Witnesses<L> = <<L as Fields>::Backend as BackendParticipants>::Witnesses;
pub type Statements<L> = <<L as Fields>::Backend as BackendParticipants>::Statements;
pub type Bodies<L> = <<L as Fields>::Backend as BackendParticipants>::Bodies;

/// The first `cells` positions belong to the frontend. The trailing two masks
/// are owned by this protocol and never become field-valued circuit inputs.
pub fn witness_count(cells: usize) -> Result<usize, String> {
    cells
        .checked_add(FINGERPRINTS)
        .ok_or_else(|| "fingerprint witness layout overflow".into())
}

pub struct Field<'a, const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling, D> {
    backend: Participant<'a, W, F, D>,
    f: &'a F,
    field_id: Vec<u8>,
    cells: usize,
}
impl<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling, D> Clone
    for Field<'_, W, F, D>
{
    fn clone(&self) -> Self {
        Self {
            backend: self.backend.clone(),
            f: self.f,
            field_id: self.field_id.clone(),
            cells: self.cells,
        }
    }
}
impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
        D: EvaluationDomain<W, F>,
    > Field<'a, W, F, D>
{
    /// `param` describes the augmented commitment, including this protocol's
    /// two cells. Frontends obtain its count with witness_count(original_count).
    /// The trusted caller supplies the canonical field representation identity,
    /// including its modulus; arithmetic fields need no packing capability.
    pub fn new(
        param: PolygeroParam,
        f: &'a F,
        domain: &'a D,
        field_id: Vec<u8>,
    ) -> Result<Self, String> {
        if field_id.is_empty() {
            return Err("empty fingerprint field identity".into());
        }
        let cells = param
            .geometry()
            .nw
            .checked_sub(FINGERPRINTS)
            .ok_or("missing fingerprint mask cells")?;
        Ok(Self {
            backend: Participant::new(param, f, domain).map_err(|e| e.to_string())?,
            f,
            field_id,
            cells,
        })
    }
}
mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl<H, T: Sealed> Sealed for (H, T) {}
}

/// Typed lists `(Field, Tail)` ending in `()` preserve every field's element
/// type. Separate binding and sampling passes fix the entire public layout
/// before drawing any coefficient, including across different fields.
pub trait Fields: sealed::Sealed + Clone {
    type Backend: BackendParticipants + Clone;
    type Coefficients;
    type Responses: Clone;
    fn backend(&self) -> Self::Backend;
    fn count(&self) -> usize;
    fn bind_layout(&self, w: &mut Writing<'_>);
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients;
    fn bind_responses(&self, responses: &Self::Responses, w: &mut Writing<'_>);
    fn authenticate(
        &self,
        statements: Statements<Self>,
        coefficients: Self::Coefficients,
        responses: &Self::Responses,
    ) -> Result<Statements<Self>, String>;
}
impl Fields for () {
    type Backend = ();
    type Coefficients = ();
    type Responses = ();
    fn backend(&self) {}
    fn count(&self) -> usize {
        0
    }
    fn bind_layout(&self, _: &mut Writing<'_>) {}
    fn coefficients(&self, _: &mut Reading<'_>) {}
    fn bind_responses(&self, _: &(), _: &mut Writing<'_>) {}
    fn authenticate(&self, _: (), _: (), _: &()) -> Result<(), String> {
        Ok(())
    }
}
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
        transcript::bind_field_layout(&self.0, w);
        self.1.bind_layout(w);
    }
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients {
        (
            transcript::field_coefficients(&self.0, r),
            self.1.coefficients(r),
        )
    }
    fn bind_responses(&self, responses: &Self::Responses, w: &mut Writing<'_>) {
        transcript::bind_field_responses(&self.0, &responses.0, w);
        self.1.bind_responses(&responses.1, w);
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

#[derive(Clone)]
pub struct Param<L: Fields> {
    fields: L,
    backend: JointPolygeroParam<L::Backend>,
}
impl<L: Fields> Param<L> {
    pub fn new(fields: L) -> Result<Self, String> {
        let backend = JointPolygeroParam::new(fields.backend()).map_err(|e| e.to_string())?;
        Ok(Self { fields, backend })
    }
    pub fn context(&self) -> Digest {
        self.backend.context()
    }
    pub fn config(&self) -> PolygeroConfig {
        self.backend.config()
    }
    pub fn commitment_context(
        &self,
    ) -> crate::runtime::v2::polygero::joint::JointCommitmentContext {
        self.backend.commitment_context()
    }
}
cfg_prover! { mod prover; pub use prover::{commit, Prover, ProverFields}; }
cfg_verifier! { mod verifier; pub use verifier::{Authenticated, Verifier}; }
