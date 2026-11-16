// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{super::Transcript, *};

impl<S: ?Sized> Opened<'_, S> {
    /// The bytes the session's current node has hashed so far: right after
    /// `new`, exactly its statement.
    pub(crate) fn statement_bytes_for_test(&self) -> &[u8] {
        self.transcript.preimage_for_test()
    }
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
