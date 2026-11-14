// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The fingerprinted field, the typed field lists, and the protocol parameters.
//!
//! The `(Field, Tail)` traversal stays in `lib`, beside the transcript framing
//! it calls.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            polygero::{
                joint::Participants as BackendParticipants, JointPolygeroParam, Participant,
                PolygeroParam,
            },
            proto::{polygero::PolygeroConfig, witness_selection::FINGERPRINTS, Digest},
            transcript::{Reading, Writing},
        },
    },
};

pub type Witnesses<L> = <<L as Fields>::Backend as BackendParticipants>::Witnesses;
pub type Statements<L> = <<L as Fields>::Backend as BackendParticipants>::Statements;
pub type Bodies<L> = <<L as Fields>::Backend as BackendParticipants>::Bodies;

/// The first `cells` positions belong to the frontend. The trailing two masks
/// are owned by this protocol and never become field-valued circuit inputs.
pub(in crate::runtime::v2) fn witness_count(cells: usize) -> Result<usize, String> {
    cells
        .checked_add(FINGERPRINTS)
        .ok_or_else(|| "fingerprint witness layout overflow".into())
}

pub struct Field<'a, const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling, D> {
    pub(super) backend: Participant<'a, W, F, D>,
    pub(super) f: &'a F,
    pub(super) field_id: Vec<u8>,
    pub(super) cells: usize,
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
    pub fn new(param: PolygeroParam, domain: &'a D, field_id: Vec<u8>) -> Result<Self, String> {
        if field_id.is_empty() {
            return Err("empty fingerprint field identity".into());
        }
        let cells = param
            .geometry()
            .nw
            .checked_sub(FINGERPRINTS)
            .ok_or("missing fingerprint mask cells")?;
        Ok(Self {
            backend: Participant::new(param, domain).map_err(|e| e.to_string())?,
            f: domain.field(),
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
    fn absorb_responses(&self, responses: &Self::Responses, w: &mut Writing<'_>);
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
    fn absorb_responses(&self, _: &(), _: &mut Writing<'_>) {}
    fn authenticate(&self, _: (), _: (), _: &()) -> Result<(), String> {
        Ok(())
    }
}

#[derive(Clone)]
pub struct Param<L: Fields> {
    pub(super) fields: L,
    pub(super) backend: JointPolygeroParam<L::Backend>,
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
}
