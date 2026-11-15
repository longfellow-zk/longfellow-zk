// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript draws of the mixed split: the nonzero `eta` and the message `mu`.
//! The framing and domain strings are those of mdoc's earlier shared-prefix
//! handoff. The split's derived weights are never absorbed.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            proto::RoundLabel,
            transcript::{Bound, Challenge, TranscriptRef},
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

/// The mixed split's nonzero rescaling challenge, drawn by the driver right
/// after the split frontend: it reads further from the frontend's last answer
/// (its last combine, after alpha and the input assertions; transcript I7),
/// with no message or boundary of its own, and the split accepts it.
pub fn eta<const W: usize, F: RuntimeField<W> + SupportsSampling, P: ?Sized>(
    t: &mut Bound<'_, P>,
    f: &F,
) -> Challenge<Eta<F::E>> {
    t.challenge(RoundLabel::Rescaling, |w| {
        let mut r = w.begin_squeeze();
        let value = loop {
            let x = r.elt_field(f);
            if !f.is_zero(&x) {
                break x;
            }
        };
        r.end_round(Eta(value))
    })
}

/// Bind the split message before any adapter challenge. The split's derived
/// weights are reconstructed by both roles and never absorbed.
pub fn absorb_mu<F: SerializableField>(t: &mut TranscriptRef<'_>, mu: &F::E, f: &F) {
    t.absorb(|w| w.write_bytes(b"native-shared-prefix/masked-opening/v2"));
    t.absorb(|w| w.write_elt_field(mu, f));
}
