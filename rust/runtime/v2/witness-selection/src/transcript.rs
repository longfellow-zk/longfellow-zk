// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 fingerprint framing and sampling shared by the prover and verifier.
//!
//! Bind the complete ordered field layout before drawing any coefficient. Every
//! vector consumes the same reading phase, and all responses bind before the
//! enclosing frontend starts. The typed field traversal stays in `lib`.
use super::{Field, Fields, FingerprintResponse, Param, FINGERPRINTS};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            proto::polygero::PolygeroCommitment,
            transcript::{Reading, RoundLabel, Transcript, Writing},
        },
    },
};

pub(super) fn bind_field_layout<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D,
>(
    field: &Field<'_, W, F, D>,
    w: &mut Writing<'_>,
) {
    w.write_bytes(&field.field_id);
    w.write_bytes(&(field.cells as u64).to_le_bytes());
    w.write_bytes(&(FINGERPRINTS as u64).to_le_bytes());
}

pub(super) fn field_coefficients<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D,
>(
    field: &Field<'_, W, F, D>,
    r: &mut Reading<'_>,
) -> [Vec<F::E>; FINGERPRINTS] {
    // Uniform, independent coordinates, not powers of one challenge. Prime
    // field rejections consume the same reader as all subsequent coordinates.
    std::array::from_fn(|_| r.elt_field_slice(field.cells, field.f))
}

pub(super) fn bind_field_responses<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D,
>(
    field: &Field<'_, W, F, D>,
    responses: &FingerprintResponse<F::E>,
    w: &mut Writing<'_>,
) {
    w.write_elt_field_slice(&responses.values, field.f);
}

impl<L: Fields> Param<L> {
    pub(super) fn challenges(
        &self,
        root: &PolygeroCommitment,
        t: &mut Transcript,
    ) -> L::Coefficients {
        t.round(RoundLabel::Fingerprint, |mut w| {
            w.write_bytes(b"longfellow/witness-selection/v1");
            w.write_bytes(&self.context().data);
            w.write_bytes(&root.root.data);
            w.write_bytes(&(self.fields.count() as u64).to_le_bytes());
            self.fields.bind_layout(&mut w);
            let mut r = w.begin_squeeze();
            let coefficients = self.fields.coefficients(&mut r);
            r.end_round(coefficients)
        })
    }

    pub(super) fn bind_responses(&self, responses: &L::Responses, t: &mut Transcript) {
        t.bind(|w| {
            w.write_bytes(b"longfellow/witness-selection/responses/v1");
            self.fields.bind_responses(responses, w);
        });
    }
}
