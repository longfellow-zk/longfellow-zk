// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript rounds of the foreign storage layer's mixed split.
//!
//! The eta and mu framing is unchanged from mdoc's earlier shared-prefix
//! handoff, whose domain strings it keeps. Adapter-mode rounds (conversion
//! challenges, masked quotients) live with their encoder in `adapter`.
use super::storage::{Group, Run, StorageMap};
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

/// Bind a mixed frontend's layout parameters before the shared root: its
/// circuit, its storage map as runs, and the bits of the split's mask R.
/// These are setup constants fixed by the trusted circuits.
pub(crate) fn absorb_storage(
    t: &mut TranscriptRef<'_>,
    circuit_id: &[u8; 32],
    storage: &StorageMap,
    mask: Group,
) {
    let word = |t: &mut TranscriptRef<'_>, x: usize| {
        t.absorb(|w| w.write_bytes(&(x as u64).to_le_bytes()))
    };
    t.absorb(|w| {
        w.write_bytes(b"foreign-storage/mixed-layout/v1");
        w.write_bytes(circuit_id);
    });
    let runs = storage.runs();
    word(t, runs.len());
    for run in runs {
        match run {
            Run::Native { first, count, cell } => {
                for x in [0, first, count, cell] {
                    word(t, x);
                }
            }
            Run::Prime {
                first,
                count,
                start,
                width,
            } => {
                for x in [1, first, count, start, width] {
                    word(t, x);
                }
            }
            Run::Coordinates { value, coordinates } => {
                for x in [2, value, coordinates.len()] {
                    word(t, x);
                }
                for c in coordinates {
                    for x in [c.index, c.group.start, c.group.width] {
                        word(t, x);
                    }
                }
            }
        }
    }
    word(t, mask.start);
    word(t, mask.width);
}
