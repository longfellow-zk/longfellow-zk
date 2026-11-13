// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One challenge block batches all completed rows. The resulting claim stays
//! local; neither its derived weights nor its target are absorbed.
use crate::runtime::{
    algebra::SupportsSampling,
    v2::{proto::RoundLabel, transcript::TranscriptRef},
};

pub(super) fn coefficients<F: SupportsSampling>(
    count: usize,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> Vec<F::E> {
    // Every frontend message is absorbed before these fresh row weights.
    // Include every layer row AND the final input equation.
    transcript.absorb(|w| w.write_bytes(b"native-masked-sumcheck/all-linear-rows/v1"));
    transcript.round(RoundLabel::RowBatching, |mut w| {
        w.write_bytes(b"all-linear-rows");
        let mut r = w.begin_squeeze();
        let rho = r.elt_field_slice(count, f);
        r.end_round(rho)
    })
}
