// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only schedule trace of a session: its messages, boundaries and
//! draws in order, the values of its index draws, and the exact bytes each
//! strand node hashed. Production
//! builds compile none of it.
use super::message::Recorded;

/// The kind of one stream read. A nonzero element is its own kind, so a
/// role that draws a plain element where the other draws a nonzero one
/// differs even when the value read is not zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Draw {
    Bytes,
    Element,
    Nonzero,
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
    /// The values of every index draw, in draw order.
    pub(crate) indices: Vec<Vec<usize>>,
}
thread_local! {
    /// While a test captures, the traces of the sessions dropped on this
    /// thread (`Trace::dropped`).
    static DROPPED: std::cell::RefCell<Option<Vec<Trace>>> = const { std::cell::RefCell::new(None) };
}
/// A session's trace is dropped with it: a verifier that rejects a proof
/// drops its session, and with it the trace of every message it absorbed and
/// every draw it made before the rejection. While a test captures, keep it.
impl Drop for Trace {
    fn drop(&mut self) {
        if self.events.is_empty() {
            return;
        }
        let _ = DROPPED.try_with(|cell| {
            if let Ok(mut dropped) = cell.try_borrow_mut() {
                if let Some(kept) = dropped.as_mut() {
                    kept.push(std::mem::take(self));
                }
            }
        });
    }
}
impl Trace {
    /// Run `f` and return its result with the traces of the sessions dropped
    /// on this thread meanwhile, in drop order.
    pub(crate) fn dropped<T>(f: impl FnOnce() -> T) -> (T, Vec<Trace>) {
        DROPPED.set(Some(Vec::new()));
        let out = f();
        (out, DROPPED.take().unwrap_or_default())
    }
    /// The first PRF block of finished node `i`: the first bytes every
    /// draw after its boundary reads, `SHA-256(u32 PRF || u64 id || digest
    /// || u64 0)` with the node's id and the digest of its preimage.
    pub(crate) fn first_block(&self, i: usize) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let node = &self.nodes[i];
        let mut input = Vec::with_capacity(52);
        input.extend(0u32.to_le_bytes());
        input.extend(&node[4..12]);
        input.extend(Sha256::digest(node));
        input.extend(0u64.to_le_bytes());
        Sha256::digest(&input).into()
    }
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
    pub(super) fn indices(&mut self, drawn: &[usize]) {
        self.indices.push(drawn.to_vec());
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
