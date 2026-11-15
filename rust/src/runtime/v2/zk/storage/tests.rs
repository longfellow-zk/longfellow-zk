// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Storage map unit tests: typed bit groups, dense native cells and runs.
use super::{ReservedSuffix, StorageMap};

#[test]
fn reserved_suffix_allocates_typed_groups_in_order() {
    let mut suffix = ReservedSuffix::new(100);
    let r = suffix.group(256).unwrap();
    let o = [suffix.word::<10>().unwrap(), suffix.word::<10>().unwrap()];
    assert_eq!((r.start, r.width), (100, 256));
    assert_eq!(o[0].group().start, 356);
    assert_eq!(o[1].group().start, 366);
    assert_eq!(suffix.len(), 276);
    let mut w = suffix.witness();
    w.set(o[1].group(), (0..10).map(|j| j == 3)).unwrap();
    assert!(w.set(o[1].group(), (0..9).map(|_| true)).is_err());
    let bits = w.into_bits();
    assert!(bits[266 + 3] && bits.iter().filter(|&&b| b).count() == 1);
}

#[test]
fn storage_map_numbers_native_cells_densely() {
    use super::{Group, Storage};
    let g = Group { start: 5, width: 1 };
    let map = StorageMap::new(4, &[(1, g)]).unwrap();
    assert_eq!(
        map.entries(),
        [
            Storage::Native(0),
            Storage::Foreign(g),
            Storage::Native(1),
            Storage::Native(2)
        ]
    );
    assert_eq!(map.native_cells(), 3);
    assert!(!map.is_pure_foreign());
    assert!(StorageMap::new(4, &[(1, g), (1, g)]).is_err());
    assert!(StorageMap::new(4, &[(4, g)]).is_err());
}

#[test]
fn storage_runs_are_maximal_and_canonical() {
    use super::{Group, Run};
    // Values 0..3 foreign with consecutive 1-bit groups at 10, 11, 12; value 3
    // jumps to bit 40; values 4..6 native.
    let g = |start| Group { start, width: 1 };
    let map = StorageMap::new(7, &[(0, g(10)), (1, g(11)), (2, g(12)), (3, g(40))]).unwrap();
    assert_eq!(
        map.runs(),
        [
            Run::Prime {
                first: 0,
                count: 3,
                start: 10,
                width: 1
            },
            Run::Prime {
                first: 3,
                count: 1,
                start: 40,
                width: 1
            },
            Run::Native {
                first: 4,
                count: 3,
                cell: 0
            },
        ]
    );
    // A change of width ends a run even when the bits are contiguous, and a
    // foreign value splits the native cells around it into two runs.
    let w = |start, width| Group { start, width };
    let map = StorageMap::new(5, &[(1, w(0, 8)), (2, w(8, 8)), (3, w(16, 4))]).unwrap();
    assert_eq!(
        map.runs(),
        [
            Run::Native {
                first: 0,
                count: 1,
                cell: 0
            },
            Run::Prime {
                first: 1,
                count: 2,
                start: 0,
                width: 8
            },
            Run::Prime {
                first: 3,
                count: 1,
                start: 16,
                width: 4
            },
            Run::Native {
                first: 4,
                count: 1,
                cell: 1
            },
        ]
    );
}

#[test]
fn groups_reject_ends_that_overflow_or_precede_the_start() {
    use super::Group;
    // A group whose end wraps would pass a naive `end <= suffix.end` check.
    assert!(Group::new(usize::MAX - 2, 4).is_err());
    assert!(Group::from_bounds(5, 4).is_err());
    assert_eq!(Group::new(usize::MAX - 4, 4).unwrap().end(), usize::MAX);
    assert_eq!(Group::from_bounds(3, 7).unwrap(), Group::new(3, 4).unwrap());
    // A valid group outside the suffix is still rejected by the witness.
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

impl super::Group {
    /// Every field: start and width. The pattern is exhaustive, so a new
    /// field does not compile until the statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> [usize; 2] {
        let Self { start, width } = *self;
        [start, width]
    }
}
impl<const N: usize> super::BitGroup<N> {
    /// Every field: the start; the width is `N`. The pattern is exhaustive,
    /// so a new field does not compile until the statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> usize {
        let Self { start } = *self;
        start
    }
}
impl StorageMap {
    /// Every field: the entries and the native cell count. The pattern is
    /// exhaustive, so a new field does not compile until the statement tests
    /// cover it.
    pub(crate) fn fields_for_test(&self) -> (&[super::Storage], usize) {
        let Self { entries, native } = self;
        (entries, *native)
    }
}
