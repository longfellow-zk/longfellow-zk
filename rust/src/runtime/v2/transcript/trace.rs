// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only schedule trace of a session: its messages, boundaries and
//! draws in order, and the exact bytes each strand node hashed. Production
//! builds compile none of it.
use super::message::Recorded;

/// The kind of one stream read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Draw {
    Bytes,
    Element,
    Indices,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Event {
    Message(Recorded),
    /// A node ended with the ROUND terminator.
    Boundary,
    /// Consecutive reads of one kind, merged.
    Draws(Draw, u64),
    /// The node ended with the SEAL terminator.
    Seal,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Trace {
    pub(crate) events: Vec<Event>,
    /// Every finished node's SHA-256 preimage, its header included.
    pub(crate) nodes: Vec<Vec<u8>>,
}
impl Trace {
    pub(super) fn message(&mut self, m: Recorded) {
        self.events.push(Event::Message(m));
    }
    pub(super) fn boundary(&mut self, node: Vec<u8>) {
        self.events.push(Event::Boundary);
        self.nodes.push(node);
    }
    pub(super) fn seal(&mut self, node: Vec<u8>) {
        self.events.push(Event::Seal);
        self.nodes.push(node);
    }
    pub(super) fn draw(&mut self, kind: Draw) {
        if let Some(Event::Draws(k, n)) = self.events.last_mut() {
            if *k == kind {
                *n += 1;
                return;
            }
        }
        self.events.push(Event::Draws(kind, 1));
    }
    /// Nodes ended by a draw; the seal is not counted.
    pub(crate) fn boundaries(&self) -> u64 {
        self.events
            .iter()
            .filter(|e| matches!(e, Event::Boundary))
            .count() as u64
    }
    /// The messages, in send order.
    pub(crate) fn messages(&self) -> impl Iterator<Item = &Recorded> {
        self.events.iter().filter_map(|e| match e {
            Event::Message(m) => Some(m),
            _ => None,
        })
    }
}

/// A prover message for transcript tests: Bytes under the `Commitment` tag.
pub(crate) struct TestMessage<'a>(pub(crate) &'a [u8]);
impl super::Message for TestMessage<'_> {
    const TAG: crate::runtime::v2::proto::tags::Tag =
        crate::runtime::v2::proto::tags::Tag::Commitment;
    fn encode(&self, e: &mut super::Encoder<'_>) {
        e.bytes(self.0);
    }
}
impl super::ProverMessage for TestMessage<'_> {}
