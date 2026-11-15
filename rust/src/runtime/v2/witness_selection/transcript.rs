// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 fingerprint challenges and responses shared by the prover and verifier.
//!
//! The statement fixes every field's layout (transcript I3). The coefficient
//! draw ends the node of the joint `Commitment`; every vector reads the same
//! stream. Each field then sends its `FingerprintResponse` before the
//! enclosing frontend starts. The typed field traversal stays in `lib`.
use super::{Field, Fields, Param};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            proto::{
                tags::Tag,
                witness_selection::{FingerprintResponse, FINGERPRINTS},
            },
            transcript::{Encoder, Message, ProverMessage, Reading, TranscriptRef},
        },
    },
};

/// `FingerprintResponse` (33): Elements(F, 2), one field's masked
/// fingerprints.
struct ResponseMessage<'a, F: SerializableField> {
    f: &'a F,
    response: &'a FingerprintResponse<F::E>,
}
impl<F: SerializableField> Message for ResponseMessage<'_, F> {
    const TAG: Tag = Tag::FingerprintResponse;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, &self.response.values);
    }
}
impl<F: SerializableField> ProverMessage for ResponseMessage<'_, F> {}

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

pub(super) fn send_field_response<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D,
>(
    field: &Field<'_, W, F, D>,
    response: &FingerprintResponse<F::E>,
    t: &mut TranscriptRef<'_>,
) {
    t.send(&ResponseMessage {
        f: field.f,
        response,
    });
}

impl<L: Fields> Param<L> {
    /// Draw every field's coefficients. The joint backend has just sent the
    /// commitment, so this ends its node.
    pub(super) fn challenges(&self, t: &mut TranscriptRef<'_>) -> L::Coefficients {
        t.draw(|r| self.fields.coefficients(r))
    }
    pub(super) fn send_responses(&self, responses: &L::Responses, t: &mut TranscriptRef<'_>) {
        self.fields.send_responses(responses, t);
    }
}
