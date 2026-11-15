// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Statement layout and masked-quotient message of the exact adapter.
use super::super::TreeShape;
use crate::{
    core::algebra::fp24::EXTENSION_DEGREE,
    runtime::v2::{
        foreign::word::MaskedWord,
        proto::tags::Tag,
        transcript::{Encoder, Header, Message, ProverMessage, SetupMessage, TranscriptRef},
        zk::storage::Group,
    },
};

struct Quotients<'a, const N: usize>(&'a [MaskedWord<N>; EXTENSION_DEGREE]);
impl<const N: usize> Message for Quotients<'_, N> {
    const TAG: Tag = Tag::ExactAdapterQuotients;
    fn encode(&self, e: &mut Encoder<'_>) {
        for m in self.0 {
            e.bits((0..N).map(|j| m.bit(j)));
        }
    }
}
impl<const N: usize> ProverMessage for Quotients<'_, N> {}

/// Send the six masked quotients before the binary sumcheck.
pub(super) fn absorb_masked<const N: usize>(
    t: &mut TranscriptRef<'_>,
    masked: &[MaskedWord<N>; EXTENSION_DEGREE],
) {
    t.send(&Quotients(masked));
}

struct Layout<'a> {
    shape: [u64; 3],
    pads: &'a [u64],
}
impl Message for Layout<'_> {
    const TAG: Tag = Tag::AdapterLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(b"longfellow/v2/foreign/fp24-ext6/exact-three-claims-per-tree/v1");
        e.nats(&self.shape);
        e.nats(self.pads);
    }
}
impl SetupMessage for Layout<'_> {}

pub(super) fn write_layout<const N: usize>(
    h: &mut Header<'_>,
    shape: TreeShape,
    pads: [Group; EXTENSION_DEGREE],
) {
    let positions: Vec<_> = pads
        .iter()
        .flat_map(|g| [g.start() as u64, g.width() as u64])
        .collect();
    h.send(&Layout {
        shape: [N as u64, shape.trees as u64, shape.leaves as u64],
        pads: &positions,
    });
}
