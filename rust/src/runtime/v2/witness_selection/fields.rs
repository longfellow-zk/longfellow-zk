// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The fingerprinted field, the typed field lists, and the protocol parameters.
//!
//! The `(Field, Tail)` traversal is in the parent module, `witness_selection`,
//! beside the transcript framing it calls.
use crate::{
    core::algebra::RegisteredField,
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            polygero::{
                JointPolygeroParam, Participant, Participants as BackendParticipants, PolygeroParam,
            },
            proto::{polygero::PolygeroConfig, witness_selection::FINGERPRINTS},
            transcript::{Reading, SessionStamp, TranscriptRef},
        },
    },
};

pub(crate) type Statements<L> = <<L as Fields>::Backend as BackendParticipants>::Statements;
pub(crate) type Bodies<L> = <<L as Fields>::Backend as BackendParticipants>::Bodies;

/// The first `cells` positions belong to the frontend. The trailing two masks
/// are owned by this protocol and never become field-valued circuit inputs.
pub(in crate::runtime::v2) fn witness_count(cells: usize) -> Result<usize, String> {
    cells
        .checked_add(FINGERPRINTS)
        .ok_or_else(|| "fingerprint witness layout overflow".into())
}

/// One field of the fingerprinted witness: its Polygero participant, its
/// field and its frontend cell count. It takes no separate field identity:
/// the statement's `CommitmentLayout` names the field (transcript I3).
pub(crate) struct Field<'a, F: RuntimeField + RegisteredField + SupportsSampling, D> {
    pub(super) backend: Participant<'a, F, D>,
    pub(super) f: &'a F,
    pub(super) cells: usize,
}
impl<F: RuntimeField + RegisteredField + SupportsSampling, D> Clone for Field<'_, F, D> {
    fn clone(&self) -> Self {
        Self {
            backend: self.backend.clone(),
            f: self.f,
            cells: self.cells,
        }
    }
}
impl<'a, F: RuntimeField + RegisteredField + SupportsSampling, D: EvaluationDomain<F>>
    Field<'a, F, D>
{
    /// `param` describes the augmented commitment, including this protocol's
    /// two cells. Frontends obtain its count with witness_count(original_count).
    /// Arithmetic fields need no packing capability.
    pub(crate) fn new(param: PolygeroParam, domain: &'a D) -> Result<Self, String> {
        let cells = param
            .geometry()
            .nw
            .checked_sub(FINGERPRINTS)
            .ok_or("missing fingerprint mask cells")?;
        Ok(Self {
            backend: Participant::new(param, domain).map_err(|e| e.to_string())?,
            f: domain.field(),
            cells,
        })
    }
}
mod sealed {
    pub(crate) trait Sealed {}
    impl Sealed for () {}
    impl<H, T: Sealed> Sealed for (H, T) {}
}

/// Typed lists `(Field, Tail)` ending in `()` preserve every field's element
/// type. Separate binding and sampling passes fix the entire public layout
/// before drawing any coefficient, including across different fields.
pub(crate) trait Fields: sealed::Sealed + Clone {
    type Backend: BackendParticipants + Clone;
    type Coefficients;
    type Responses: Clone;
    fn backend(&self) -> Self::Backend;
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients;
    fn send_responses(&self, responses: &Self::Responses, t: &mut TranscriptRef<'_>);
    /// Each field's frontend equations followed by its `FINGERPRINTS`
    /// fingerprint equations, built from the coefficients and responses of
    /// the commitment. It rejects equations derived on a session other than
    /// `session` or reaching outside the frontend's cells. Only the
    /// completion of the opening (`Prover::finish`, `Verifier::finish`) calls
    /// it.
    fn authenticate(
        &self,
        statements: Statements<Self>,
        coefficients: Self::Coefficients,
        responses: &Self::Responses,
        session: &SessionStamp,
    ) -> Result<Statements<Self>, String>;
}
impl Fields for () {
    type Backend = ();
    type Coefficients = ();
    type Responses = ();
    fn backend(&self) {}
    fn coefficients(&self, _: &mut Reading<'_>) {}
    fn send_responses(&self, _: &(), _: &mut TranscriptRef<'_>) {}
    fn authenticate(&self, _: (), _: (), _: &(), _: &SessionStamp) -> Result<(), String> {
        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct Param<L: Fields> {
    pub(super) fields: L,
    pub(super) backend: JointPolygeroParam<L::Backend>,
}
impl<L: Fields> Param<L> {
    /// The parameter of a joint statement's fields. Only the joint ZK
    /// parameter builds one, from the participants that write the statement's
    /// `CommitmentLayout`s (witness_selection I2).
    pub(crate) fn new(fields: L) -> Result<Self, String> {
        let backend = JointPolygeroParam::new(fields.backend()).map_err(|e| e.to_string())?;
        Ok(Self { fields, backend })
    }
    pub(crate) fn config(&self) -> PolygeroConfig {
        self.backend.config()
    }
}
