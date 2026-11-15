// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript steps of the P-256 adapter: the conversion challenges and the
//! masked quotients. The statement fixes the adapter's layout
//! (`AdapterLayout`); derived leaf coefficients are never absorbed.
use crate::runtime::{
    algebra::p256::{P256Element, P256Field},
    v2::{
        foreign::{adapter::TreeShape, word::MaskedWord},
        proto::tags::Tag,
        transcript::{
            Bound, Challenge, Encoder, Header, Message, ProverMessage, Reading, SetupMessage,
            TranscriptRef,
        },
        zk::storage::Group,
    },
};

/// The P-256 adapter's conversion pair, each nonzero. Only its draw
/// (`draw_conversion`) builds it.
pub struct Conversion(pub(super) [P256Element; 2]);

/// `P256AdapterQuotients` (65): Bits(Q), Bits(Q), the two masked quotient
/// words, each least significant bit first.
struct QuotientsMessage<'a, const Q: usize>(&'a [MaskedWord<Q>; 2]);
impl<const Q: usize> Message for QuotientsMessage<'_, Q> {
    const TAG: Tag = Tag::P256AdapterQuotients;
    fn encode(&self, e: &mut Encoder<'_>) {
        for m in self.0 {
            e.bits((0..Q).map(|j| m.bit(j)));
        }
    }
}
impl<const Q: usize> ProverMessage for QuotientsMessage<'_, Q> {}

fn draw_pair(r: &mut Reading<'_>, p: &P256Field) -> [P256Element; 2] {
    std::array::from_fn(|_| r.nonzero(p))
}

/// Two independent nonzero full-field conversion challenges. Wrapping mode
/// needs both: one rescaling leaves a false claim about 2^-117 to survive.
/// They are drawn from the boundary after the split message. Protocol code
/// draws them as the adapter's input challenge (`draw_conversion`); this
/// raw draw is for the tests that check that both are the same.
#[cfg(test)]
pub(in crate::runtime::v2::foreign) fn conversion(
    t: &mut TranscriptRef<'_>,
    p: &P256Field,
) -> [P256Element; 2] {
    t.draw(|r| draw_pair(r, p))
}

/// The same draw as `conversion`, as the adapter's input challenge.
pub(super) fn draw_conversion<P: ?Sized>(
    t: &mut Bound<'_, P>,
    p: &P256Field,
) -> Challenge<Conversion> {
    t.challenge(|r| Conversion(draw_pair(r, p)))
}

/// Send both masked quotients before the binary sumcheck. Their width is
/// fixed by the instance type. Only the mode's `prove` and `verify` send
/// them.
pub(in crate::runtime::v2::foreign) fn send_quotients<const Q: usize>(
    t: &mut TranscriptRef<'_>,
    masked: &[MaskedWord<Q>; 2],
) {
    t.send(&QuotientsMessage(masked));
}

/// The mode ID of the P-256 adapter.
const P256_MODE_ID: &[u8] = b"longfellow/v2/foreign/p256/two-full-field-trees/v1";

/// `AdapterLayout` (22): Bytes mode ID; Nats(Q, tree count, virtual leaves
/// per tree); Nats(start and width of each quotient pad's bits among the
/// binary inputs, in tree order). The split mask R's bits are in the split
/// participant's `CommitmentLayout`, so they are not repeated here.
struct LayoutMessage<'a> {
    id: &'a [u8],
    shape: [u64; 3],
    pads: &'a [u64],
}
impl Message for LayoutMessage<'_> {
    const TAG: Tag = Tag::AdapterLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(self.id);
        e.nats(&self.shape);
        e.nats(self.pads);
    }
}
impl SetupMessage for LayoutMessage<'_> {}

/// Write the P-256 mode's `AdapterLayout`: its quotient width `Q`, its tree
/// shape, and its two quotient pads' bit groups.
pub(super) fn write_layout<const Q: usize>(h: &mut Header<'_>, shape: TreeShape, pads: [Group; 2]) {
    let positions: Vec<u64> = pads
        .iter()
        .flat_map(|g| [g.start() as u64, g.width() as u64])
        .collect();
    h.send(&LayoutMessage {
        id: P256_MODE_ID,
        shape: [Q as u64, shape.trees as u64, shape.leaves as u64],
        pads: &positions,
    });
}
