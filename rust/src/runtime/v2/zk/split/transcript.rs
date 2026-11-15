// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript steps of the mixed split: the nonzero `eta` and the message
//! `mu`. The split's derived weights are never absorbed.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            proto::tags::Tag,
            transcript::{Bound, Challenge, Encoder, Message, ProverMessage, TranscriptRef},
        },
    },
};

/// The mixed split's nonzero rescaling challenge `eta`. Only its draw
/// (`eta`) builds it.
pub struct Eta<E>(pub(super) E);
impl<E> Eta<E> {
    pub fn value(&self) -> &E {
        &self.0
    }
}

/// `SplitOpening` (64): Elements(F, 1), the split message mu (F is P-256 in
/// mdoc).
struct OpeningMessage<'a, F: SerializableField> {
    f: &'a F,
    mu: &'a F::E,
}
impl<F: SerializableField> Message for OpeningMessage<'_, F> {
    const TAG: Tag = Tag::SplitOpening;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, std::slice::from_ref(self.mu));
    }
}
impl<F: SerializableField> ProverMessage for OpeningMessage<'_, F> {}

/// The mixed split's nonzero rescaling challenge, drawn by the driver right
/// after the split frontend: it reads further from the frontend's last answer
/// (its last combine, after alpha and the input assertions; transcript I7),
/// with no message or boundary of its own, and the split accepts it.
pub fn eta<const W: usize, F: RuntimeField<W> + SupportsSampling, P: ?Sized>(
    t: &mut Bound<'_, P>,
    f: &F,
) -> Challenge<Eta<F::E>> {
    t.challenge(|r| {
        Eta(loop {
            let x = r.elt_field(f);
            if !f.is_zero(&x) {
                break x;
            }
        })
    })
}

/// Send the split message before any adapter challenge. The split's derived
/// weights are reconstructed by both roles and never absorbed.
pub fn send_mu<F: SerializableField>(t: &mut TranscriptRef<'_>, mu: &F::E, f: &F) {
    t.send(&OpeningMessage { f, mu });
}
