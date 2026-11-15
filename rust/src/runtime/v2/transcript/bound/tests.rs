// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{super::Transcript, *};
use crate::runtime::v2::transcript::TestMessage;

impl<S: ?Sized> Opened<'_, S> {
    /// The bytes the session's current node has hashed so far: right after
    /// `new`, exactly its statement.
    pub(crate) fn statement_bytes_for_test(&self) -> &[u8] {
        self.transcript.preimage_for_test()
    }
}

fn draw(t: &mut Bound<'_, [u8; 3]>) -> Challenge<Vec<u8>> {
    t.transcript().send(&TestMessage(b"message"));
    t.challenge(|r| r.bytes(16))
}

#[test]
fn part_is_the_value_bound_and_projects_to_its_fields() {
    let statement = ([1u8, 2, 3], 7u64);
    let mut t = Transcript::for_test(b"bound/part");
    let mut b = t.bound(&statement);
    assert!(std::ptr::eq(b.part(), &statement));
    let p = b.project(|s| &s.0);
    assert!(std::ptr::eq(p.part(), &statement.0));
    assert_eq!(p.part(), &[1, 2, 3]);
}

#[test]
fn challenge_is_accepted_where_it_was_drawn_and_matches_the_plain_round() {
    let part = [0u8; 3];
    let mut t = Transcript::for_test(b"bound/accept");
    let mut b = t.bound(&part);
    let c = draw(&mut b);
    let value = b.accept(c).unwrap();
    // Stamping changes no transcript byte: the same round drawn directly
    // yields the same value and leaves the session in the same state.
    let mut plain = Transcript::for_test(b"bound/accept");
    plain.send_for_test(b"message");
    let expected = plain.bytes(16);
    assert_eq!(value, expected);
    assert_eq!(t.bytes(32), plain.bytes(32));
}

#[test]
fn a_message_sent_after_the_draw_makes_the_challenge_stale() {
    let part = [0u8; 3];
    let mut t = Transcript::for_test(b"bound/stale");
    let mut b = t.bound(&part);
    let c = draw(&mut b);
    b.transcript().send(&TestMessage(b"late"));
    assert_eq!(b.accept(c).unwrap_err(), StaleChallenge);
}

#[test]
fn a_later_boundary_makes_the_challenge_stale() {
    let part = [0u8; 3];
    let mut t = Transcript::for_test(b"bound/later");
    let mut b = t.bound(&part);
    let early = draw(&mut b);
    let late = draw(&mut b);
    assert_eq!(b.accept(early).unwrap_err(), StaleChallenge);
    assert!(b.accept(late).is_ok());
}

#[test]
fn a_challenge_from_another_transcript_is_rejected() {
    let part = [0u8; 3];
    let mut a = Transcript::for_test(b"bound/a");
    let mut b = Transcript::for_test(b"bound/b");
    let c = draw(&mut a.bound(&part));
    // `b` stands at a boundary with the same index and message count; only
    // the node digest tells the sessions apart.
    let mut bb = b.bound(&part);
    let own = draw(&mut bb);
    assert_eq!(bb.accept(c).unwrap_err(), StaleChallenge);
    assert!(bb.accept(own).is_ok());
}

#[test]
fn a_challenge_from_a_session_with_an_equal_history_is_rejected() {
    // Equal statements and messages give equal positions and equal values;
    // only the session identity tells the sessions apart.
    let part = [0u8; 3];
    let mut a = Transcript::for_test(b"bound/equal");
    let mut b = Transcript::for_test(b"bound/equal");
    let from_a = draw(&mut a.bound(&part));
    let own = draw(&mut b.bound(&part));
    assert!(a.position() == b.position());
    let bb = b.bound(&part);
    assert_eq!(bb.accept(from_a).unwrap_err(), StaleChallenge);
    let value = bb.accept(own).unwrap();
    // A fork has the same history and a fresh identity.
    let mut fork = a.fork_for_test();
    let from_fork = draw(&mut fork.bound(&part));
    let at_a = draw(&mut a.bound(&part));
    let ab = a.bound(&part);
    assert_eq!(ab.accept(from_fork).unwrap_err(), StaleChallenge);
    assert!(ab.accept(at_a).is_ok());
    let mut plain = Transcript::for_test(b"bound/equal");
    plain.send_for_test(b"message");
    assert_eq!(value, plain.bytes(16));
}

#[test]
fn every_session_has_its_own_stamp() {
    let part = ();
    let mut a = Transcript::for_test(b"bound/session");
    let mut b = Transcript::for_test(b"bound/session");
    let stamp = a.bound(&part).session();
    assert_eq!(stamp, a.bound(&part).session());
    a.bytes(1);
    assert_eq!(stamp, a.bound(&part).session());
    assert_ne!(stamp, b.bound(&part).session());
    assert_ne!(stamp, a.fork_for_test().bound(&part).session());
}

#[test]
fn draws_that_continue_the_stream_keep_the_challenge_fresh() {
    // A draw with no message since the boundary reads further from the same
    // node (transcript I7), so both challenges stand at that boundary.
    let part = [0u8; 3];
    let mut t = Transcript::for_test(b"bound/continue");
    let mut b = t.bound(&part);
    let first = draw(&mut b);
    let second = b.challenge(|r| r.bytes(16));
    let second_value = b.accept(second).unwrap();
    let first_value = b.accept(first).unwrap();
    let mut plain = Transcript::for_test(b"bound/continue");
    plain.send_for_test(b"message");
    let expected = plain.bytes(32);
    assert_eq!([first_value, second_value].concat(), expected);
}
