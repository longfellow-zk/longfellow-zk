// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trace-zero messages and challenges. The statement fixes the packing
//! parameters and cell counts (transcript I3), and ZK derives the source
//! claim from earlier messages and challenges on this same transcript, so
//! dual packing absorbs only its two messages: `PackingU`, then the delta
//! challenges, then `PackingA`.
use crate::{
    core::algebra::{RegisteredField, SerializableField},
    runtime::{
        algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
        v2::{
            proto::tags::Tag,
            transcript::{Encoder, Message, ProverMessage, TranscriptRef},
        },
    },
};

/// `PackingU` (80): Elements(F, m), the trace-zero responses, m the packing
/// degree.
struct UMessage<'a, F: RegisteredField> {
    f: &'a F,
    u: &'a [F::E],
}
impl<F: RegisteredField> Message for UMessage<'_, F> {
    const TAG: Tag = Tag::PackingU;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, self.u);
    }
}
impl<F: RegisteredField> ProverMessage for UMessage<'_, F> {}

/// `PackingA` (81): Elements(F, 1), the trace-zero mask response.
struct AMessage<'a, F: RegisteredField> {
    f: &'a F,
    a: &'a F::E,
}
impl<F: RegisteredField> Message for AMessage<'_, F> {
    const TAG: Tag = Tag::PackingA;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, std::slice::from_ref(self.a));
    }
}
impl<F: RegisteredField> ProverMessage for AMessage<'_, F> {}

/// Send U, then draw the m independent delta challenges from its boundary.
pub(super) fn challenges<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
    ts: &mut TranscriptRef<'_>,
) -> Vec<E<X>>
where
    X::Ambient: SerializableField,
{
    ts.send(&UMessage { f: p.field(), u });
    ts.draw(|r| (0..p.degree()).map(|_| r.elt_field(p.field())).collect())
}
/// Send A. It may depend on delta, but it must be fixed before the backend
/// draws the challenges that authenticate the two resulting linear equations.
pub(super) fn finish<X: PackingExtension>(
    p: &PackingParameters<X>,
    a: &E<X>,
    ts: &mut TranscriptRef<'_>,
) where
    X::Ambient: SerializableField,
{
    ts.send(&AMessage { f: p.field(), a });
}
