// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Storage map unit tests: typed bit groups, dense native cells and runs.
use super::{ReservedSuffix, StorageMap};

#[test]
fn reserved_suffix_allocates_typed_groups_in_order() {
    let mut suffix = ReservedSuffix::new(100);
    let r = suffix.group(256);
    let o = [suffix.word::<10>(), suffix.word::<10>()];
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
