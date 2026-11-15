// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript steps of the split: the mixed split's nonzero `eta` and message
//! `mu`, and the pure-foreign row weights. The split's derived weights are
//! never absorbed.
use crate::{
    core::algebra::RegisteredField,
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

/// The pure-foreign row weights rho_0..rho_L: one per layer row, then one
/// for the input equation. Only `row_weights` builds them, and only the pure
/// branch, `SplitClaim::batch`, accepts them.
pub struct RowWeights<E>(pub(super) Vec<E>);

/// `SplitOpening` (64): Elements(F, 1), the split message mu (F is P-256 in
/// mdoc).
struct OpeningMessage<'a, F: RegisteredField> {
    f: &'a F,
    mu: &'a F::E,
}
impl<F: RegisteredField> Message for OpeningMessage<'_, F> {
    const TAG: Tag = Tag::SplitOpening;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, std::slice::from_ref(self.mu));
    }
}
impl<F: RegisteredField> ProverMessage for OpeningMessage<'_, F> {}

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

/// `count` pure-foreign row weights (`SplitClaim::row_weight_count`), drawn
/// by the driver right after the split frontend: they read further from the frontend's last answer
/// (its last combine, after alpha and the input assertions; transcript I7),
/// with no message or boundary of their own, and `SplitClaim::batch`
/// accepts them.
pub fn row_weights<F: SupportsSampling, P: ?Sized>(
    t: &mut Bound<'_, P>,
    count: usize,
    f: &F,
) -> Challenge<RowWeights<F::E>> {
    t.challenge(|r| RowWeights(r.elt_field_slice(count, f)))
}

/// Send the split message before any adapter challenge. The split's derived
/// weights are reconstructed by both roles and never absorbed.
pub fn send_mu<F: RegisteredField>(t: &mut TranscriptRef<'_>, mu: &F::E, f: &F) {
    t.send(&OpeningMessage { f, mu });
}
