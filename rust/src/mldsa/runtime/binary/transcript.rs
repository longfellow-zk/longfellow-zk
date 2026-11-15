// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::SerializableField,
    runtime::v2::{
        proto::{tags::Tag, witness_selection::FINGERPRINTS},
        transcript::{Encoder, Header, Message, SetupMessage},
    },
};
impl BinaryParticipant {
    /// Write each immutable source and layout before the commitment.
    pub(in crate::mldsa::runtime) fn write_layout(&self, h: &mut Header<'_>) {
        h.send(&BinaryLayout(self));
        if let Some(s) = &self.simd {
            s.program().write_layout(h);
        } else {
            h.send(&PackingLayoutMessage(self));
        }
    }
}
struct BinaryLayout<'a>(&'a BinaryParticipant);
impl Message for BinaryLayout<'_> {
    const TAG: Tag = Tag::MldsaBinaryLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(&self.0.fragment_id);
        e.nats(
            &self
                .0
                .geometry
                .sumcheck()
                .layers()
                .iter()
                .map(|&x| x as u64)
                .collect::<Vec<_>>(),
        );
    }
}
impl SetupMessage for BinaryLayout<'_> {}
struct PackingLayoutMessage<'a>(&'a BinaryParticipant);
impl Message for PackingLayoutMessage<'_> {
    const TAG: Tag = Tag::CommitmentLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        let b = &self.0.backend;
        e.nats(&[
            b.parameters.field().field_id() as u64,
            b.layout.private_inputs as u64,
            b.layout.pad_cells as u64,
            FINGERPRINTS as u64,
        ]);
        e.bytes(&b.parameters.descriptor());
        e.nats(&[]);
        e.nats(&[]);
        e.nats(&[0, 0]);
    }
}
impl SetupMessage for PackingLayoutMessage<'_> {}
