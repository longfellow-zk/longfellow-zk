// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One challenge block batches all completed rows; the resulting claim binds
//! before the adapter's separate rescaling round. Both roles use this order.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::SupportsSampling,
        v2::transcript::{RoundLabel, TranscriptRef},
    },
};

pub(super) fn coefficients<F: SupportsSampling>(
    count: usize,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> Vec<F::E> {
    // All masked prime messages have already been absorbed before these fresh
    // row weights. Include every layer row AND the final input equation.
    transcript.bind(|w| w.write_bytes(b"native-masked-sumcheck/all-linear-rows/v1"));
    transcript.round(RoundLabel::RowBatching, |mut w| {
        w.write_bytes(b"all-linear-rows");
        let mut r = w.begin_squeeze();
        let rho = r.elt_field_slice(count, f);
        r.end_round(rho)
    })
}

pub(super) fn bind_claim<F: SerializableField>(
    weights: &[F::E],
    target: &F::E,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) {
    // Explicitly fix the complete adapter statement before its rescaling alpha.
    transcript.bind(|w| {
        w.write_bytes(b"native-masked-sumcheck/fixed-linear-claim/v1");
        w.write_bytes(&(weights.len() as u64).to_le_bytes());
    });
    transcript.bind(|w| {
        w.write_elt_field_slice(weights, f);
        w.write_elt_field(target, f);
    });
}
