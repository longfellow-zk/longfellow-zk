// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript rounds of the mixed split: the nonzero `eta` and the message `mu`.
//! The framing and domain strings are those of mdoc's earlier shared-prefix
//! handoff. The split's derived weights are never absorbed.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{proto::RoundLabel, transcript::TranscriptRef},
    },
};

/// The mixed split's nonzero rescaling challenge.
pub fn eta<const W: usize, F: RuntimeField<W> + SupportsSampling>(
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> F::E {
    t.round(RoundLabel::Rescaling, |mut w| {
        w.write_bytes(b"native-shared-prefix/nonzero-rescaling/v2");
        let mut r = w.begin_squeeze();
        let value = loop {
            let x = r.elt_field(f);
            if !f.is_zero(&x) {
                break x;
            }
        };
        r.end_round(value)
    })
}

/// Bind the split message before any adapter challenge. The split's derived
/// weights are reconstructed by both roles and never absorbed.
pub fn absorb_mu<F: SerializableField>(t: &mut TranscriptRef<'_>, mu: &F::E, f: &F) {
    t.absorb(|w| w.write_bytes(b"native-shared-prefix/masked-opening/v2"));
    t.absorb(|w| w.write_elt_field(mu, f));
}
