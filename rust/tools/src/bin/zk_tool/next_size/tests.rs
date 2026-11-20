// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn frontier_for_unpadded_tree() {
    // The isolated leaf is one edge from the root; the other two are two.
    assert_eq!(expected_frontier(3, 1), Q::ratio(5, 3));
    assert_eq!(expected_frontier(3, 2), Q::int(1));
    assert_eq!(expected_frontier(3, 3), Q::int(0));
}

#[test]
fn next_profile_certificate() {
    let p = next_size_profile().unwrap();
    assert_eq!((p.k, p.s, p.n, p.t), (347, 12, 2429, 84));
    assert!(expected_frontier(p.n, p.t) < expected_frontier(MDOC_JOINT_PROFILE.n, p.t));
}
