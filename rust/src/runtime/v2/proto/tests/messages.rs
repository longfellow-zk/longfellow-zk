// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Every prover message is absorbed where it is sent, before the next draw
//! (transcript I4, I7).
//!
//! The checks alter one byte of a prover message where the proof carries
//! it, run the complete verifier on the altered proof and read the trace of
//! the session it drops when it rejects: the verifier must absorb the
//! altered value as that message, end the message's node with a draw, and so
//! draw a different next challenge; and it must reject the proof.
use crate::runtime::v2::transcript::{Event, Trace};

/// One prover message of a trace: its index among the trace's messages, its
/// tag, where its payload lies in the proof, and the node that holds it,
/// whose boundary the next draw follows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Sent {
    pub(crate) index: usize,
    pub(crate) tag: u64,
    pub(crate) offset: usize,
    pub(crate) len: usize,
    pub(crate) node: usize,
}

/// Whether `tag` is a prover message's: after the statement, before the seal.
fn prover(tag: u64) -> bool {
    (32..112).contains(&tag)
}

/// The prover messages of `trace` with their proof locations. Their
/// payloads, in send order, are the proof's interactive section from
/// `start` (`check_trace_matches_wire`).
pub(crate) fn sent(trace: &Trace, start: usize) -> Vec<Sent> {
    let (mut index, mut node, mut offset) = (0, 0, start);
    let mut out = Vec::new();
    for event in &trace.events {
        match event {
            Event::Message(m) => {
                if prover(m.tag) {
                    let len = m.payload.len();
                    out.push(Sent {
                        index,
                        tag: m.tag,
                        offset,
                        len,
                        node,
                    });
                    offset += len;
                }
                index += 1;
            }
            Event::Boundary => node += 1,
            Event::Draws(..) | Event::Seal => {}
        }
    }
    out
}

/// Whether a draw follows the boundary that ends node `node` of `trace`.
fn drawn_after(trace: &Trace, node: usize) -> bool {
    let mut events = trace
        .events
        .iter()
        .skip_while({
            let mut boundaries = 0;
            move |e| {
                if matches!(e, Event::Boundary) {
                    boundaries += 1;
                }
                boundaries <= node
            }
        })
        .skip(1);
    matches!(events.next(), Some(Event::Draws(..)))
}

/// Alter the first payload byte of `m`, a prover message of `honest` (the
/// trace of the complete verification of `proof`), where `proof` carries
/// it, and check the verification of the altered proof. `verify` runs the
/// complete verifier on a proof and returns whether it accepted it and the
/// traces of the sessions dropped meanwhile (`Trace::dropped`).
pub(crate) fn check_absorbed(
    honest: &Trace,
    proof: &[u8],
    m: &Sent,
    verify: &impl Fn(&[u8]) -> (bool, Vec<Trace>),
) {
    let what = format!(
        "message {} (tag {}, proof byte {})",
        m.index, m.tag, m.offset
    );
    let mut altered = proof.to_vec();
    altered[m.offset] ^= 1;
    let (accepted, traces) = verify(&altered);
    assert!(!accepted, "{what}: the altered proof verifies");
    let [t] = &traces[..] else {
        panic!("{what}: {} sessions dropped", traces.len())
    };
    // The verifier absorbed the altered byte as this message, after the
    // same messages as before.
    let ours: Vec<_> = t.messages().collect();
    let theirs: Vec<_> = honest.messages().collect();
    assert!(
        ours.len() > m.index,
        "{what}: rejected before it was absorbed"
    );
    assert!(
        ours[..m.index] == theirs[..m.index],
        "{what}: earlier messages"
    );
    let mut expected = theirs[m.index].clone();
    expected.payload[0] ^= 1;
    assert_eq!(*ours[m.index], expected, "{what}: absorbed value");
    // It ended the message's node and drew from it: the earlier nodes are
    // unchanged and the next challenge is not.
    assert!(
        t.nodes.len() > m.node,
        "{what}: rejected before the next draw"
    );
    assert!(
        drawn_after(t, m.node) && drawn_after(honest, m.node),
        "{what}: draw"
    );
    assert!(
        t.nodes[..m.node] == honest.nodes[..m.node],
        "{what}: earlier nodes"
    );
    assert_ne!(
        t.first_block(m.node),
        honest.first_block(m.node),
        "{what}: the next challenge"
    );
}
