// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{super::Transcript, *};

const ROUND: u8 = 6;

fn draw(t: &mut Bound<'_, [u8; 3]>) -> Challenge<Vec<u8>> {
    t.challenge(ROUND, |mut w| {
        w.write_bytes(b"message");
        let mut r = w.begin_squeeze();
        let x = r.bytes(16);
        r.end_round(x)
    })
}

#[test]
fn part_is_the_value_bound_and_projects_to_its_fields() {
    let statement = ([1u8, 2, 3], 7u64);
    let mut t = Transcript::new(b"bound/part");
    let mut b = t.bound(&statement);
    assert!(std::ptr::eq(b.part(), &statement));
    let p = b.project(|s| &s.0);
    assert!(std::ptr::eq(p.part(), &statement.0));
    assert_eq!(p.part(), &[1, 2, 3]);
}

#[test]
fn challenge_is_accepted_where_it_was_drawn_and_matches_the_plain_round() {
    let part = [0u8; 3];
    let mut t = Transcript::new(b"bound/accept");
    let mut b = t.bound(&part);
    let c = draw(&mut b);
    let value = b.accept(c).unwrap();
    // Stamping changes no transcript byte: the same round drawn directly
    // yields the same value and leaves the session in the same state.
    let mut plain = Transcript::new(b"bound/accept");
    let expected = plain.borrow().round(ROUND, |mut w| {
        w.write_bytes(b"message");
        let mut r = w.begin_squeeze();
        let x = r.bytes(16);
        r.end_round(x)
    });
    assert_eq!(value, expected);
    assert_eq!(t.bytes(32), plain.bytes(32));
}

#[test]
fn a_message_sent_after_the_draw_makes_the_challenge_stale() {
    let part = [0u8; 3];
    let mut t = Transcript::new(b"bound/stale");
    let mut b = t.bound(&part);
    let c = draw(&mut b);
    b.transcript().absorb(|w| w.write_bytes(b"late"));
    assert_eq!(b.accept(c).unwrap_err(), StaleChallenge);
}

#[test]
fn a_later_boundary_makes_the_challenge_stale() {
    let part = [0u8; 3];
    let mut t = Transcript::new(b"bound/later");
    let mut b = t.bound(&part);
    let early = draw(&mut b);
    let late = draw(&mut b);
    assert_eq!(b.accept(early).unwrap_err(), StaleChallenge);
    assert!(b.accept(late).is_ok());
}

#[test]
fn a_challenge_from_another_transcript_is_rejected() {
    let part = [0u8; 3];
    let mut a = Transcript::new(b"bound/a");
    let mut b = Transcript::new(b"bound/b");
    let c = draw(&mut a.bound(&part));
    // `b` stands at a boundary with the same index and message count; only
    // the node digest tells the sessions apart.
    let mut bb = b.bound(&part);
    let own = draw(&mut bb);
    assert_eq!(bb.accept(c).unwrap_err(), StaleChallenge);
    assert!(bb.accept(own).is_ok());
}

#[test]
fn every_session_has_its_own_stamp() {
    let part = ();
    let mut a = Transcript::new(b"bound/session");
    let mut b = Transcript::new(b"bound/session");
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
    let mut t = Transcript::new(b"bound/continue");
    let mut b = t.bound(&part);
    let first = draw(&mut b);
    let second = b.challenge(ROUND, |w| {
        let mut r = w.begin_squeeze();
        let x = r.bytes(16);
        r.end_round(x)
    });
    let second_value = b.accept(second).unwrap();
    let first_value = b.accept(first).unwrap();
    let mut plain = Transcript::new(b"bound/continue");
    let expected = plain.borrow().round(ROUND, |mut w| {
        w.write_bytes(b"message");
        let mut r = w.begin_squeeze();
        let x = r.bytes(32);
        r.end_round(x)
    });
    assert_eq!([first_value, second_value].concat(), expected);
}
