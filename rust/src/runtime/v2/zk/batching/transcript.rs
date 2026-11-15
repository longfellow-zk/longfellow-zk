// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One challenge block batches all completed rows. The resulting claim stays
//! local; neither its derived weights nor its target are absorbed.
use crate::runtime::{algebra::SupportsSampling, v2::transcript::TranscriptRef};

pub(super) fn coefficients<F: SupportsSampling>(
    count: usize,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> Vec<F::E> {
    // Every frontend message precedes these fresh row weights, which read
    // further from the frontend's last boundary (transcript I7, I8).
    // Include every layer row AND the final input equation.
    transcript.draw(|r| r.elt_field_slice(count, f))
}
