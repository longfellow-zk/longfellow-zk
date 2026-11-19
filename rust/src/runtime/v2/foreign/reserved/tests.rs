// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Reserved suffix unit tests: typed groups in allocation order, and ends
//! that would overflow.
use super::{BitGroup, ReservedSuffix};
use crate::runtime::v2::zk::storage::Group;

#[test]
fn reserved_suffix_allocates_typed_groups_in_order() {
    let mut suffix = ReservedSuffix::new(100);
    let r = suffix.group(256).unwrap();
    let o = [suffix.word::<10>().unwrap(), suffix.word::<10>().unwrap()];
    assert_eq!((r.start(), r.width()), (100, 256));
    assert_eq!(o[0].group().start(), 356);
    assert_eq!(o[1].group().start(), 366);
    assert_eq!(suffix.len(), 276);
    let mut w = suffix.witness();
    w.set(o[1].group(), (0..10).map(|j| j == 3)).unwrap();
    assert!(w.set(o[1].group(), (0..9).map(|_| true)).is_err());
    let bits = w.into_bits();
    assert!(bits[266 + 3] && bits.iter().filter(|&&b| b).count() == 1);
}

#[test]
fn reserved_witness_rejects_a_group_outside_the_suffix() {
    // A valid group whose end is the end of memory lies outside the suffix:
    // the witness rejects it rather than computing a wrapped offset.
    let mut suffix = ReservedSuffix::new(100);
    suffix.group(8).unwrap();
    let mut w = suffix.witness();
    let far = Group::new(usize::MAX - 4, 4).unwrap();
    assert!(w.set(far, [true; 4]).is_err());
}

#[test]
fn reserved_suffix_rejects_advancing_past_the_end_of_memory() {
    let mut suffix = ReservedSuffix::new(usize::MAX - 1);
    assert!(suffix.group(4).is_err());
    assert!(suffix.word::<4>().is_err());
    // A rejected allocation leaves the suffix unchanged.
    assert_eq!(suffix.end(), usize::MAX - 1);
    assert!(suffix.is_empty());
    assert_eq!(suffix.group(1).unwrap().end(), usize::MAX);
}

impl<const N: usize> BitGroup<N> {
    /// Every field: the group, whose width is `N`. The pattern is
    /// exhaustive, so a new field does not compile until the statement
    /// tests cover it.
    pub(crate) fn fields_for_test(&self) -> usize {
        let Self(group) = *self;
        group.start()
    }
}
