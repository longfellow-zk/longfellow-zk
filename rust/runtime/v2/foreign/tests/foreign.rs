// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Foreign storage unit tests: typed words, the fixed fragment and leaves.
use super::{
    adapter::{fragment, virtual_inputs, Leaf, TreeInstance, TreeShape},
    storage::{ReservedSuffix, StorageMap},
    word::{MaskedWord, Otp, Word},
};
use crate::{
    core::algebra::{AlgebraicField, SupportsU128Conversions},
    runtime::{algebra::gf2_128::Gf2_128Field, random::DeterministicRng},
};

#[test]
fn masked_word_codec_is_canonical() {
    let mut rng = DeterministicRng::new(7);
    let k = Word::<10>::new(0x2a5).unwrap();
    assert!(Word::<10>::new(1 << 10).is_err());
    let o = Otp::<10>::sample(&mut rng);
    let m = MaskedWord::mask(k, &o);
    let bytes = m.encoded();
    assert_eq!(bytes.len(), 2);
    let mut read = bytes.as_slice();
    assert_eq!(MaskedWord::<10>::read(&mut read).unwrap(), m);
    assert!(read.is_empty());
    // Any nonzero padding bit is rejected.
    for bit in 2..8 {
        let mut bad = bytes.clone();
        bad[1] |= 1 << bit;
        assert!(MaskedWord::<10>::read(&mut bad.as_slice()).is_err());
    }
    assert!(MaskedWord::<10>::read(&mut &bytes[..1]).is_err());
    // Unmasking recovers k bit by bit.
    let pad: Vec<_> = o.bits().collect();
    for (j, &p) in pad.iter().enumerate() {
        assert_eq!(m.bit(j) ^ p, (k.value() >> j) & 1 != 0);
    }
}

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
    use super::storage::{Coordinate, Group, Storage};
    let g = Group { start: 5, width: 1 };
    let map = StorageMap::new(4, &[(1, g)]).unwrap();
    assert_eq!(
        map.entries(),
        [
            Storage::Native(0),
            Storage::Foreign(vec![Coordinate { index: 0, group: g }]),
            Storage::Native(1),
            Storage::Native(2)
        ]
    );
    assert!(StorageMap::new(4, &[(1, g), (1, g)]).is_err());
    let two = StorageMap::with_coordinates(2, &[(0, 0, g), (0, 3, g)]).unwrap();
    assert_eq!(two.native_cells(), 1);
    assert!(two.entries()[0].prime_group().is_none());
}

#[test]
fn fragment_accepts_exactly_unit_products() {
    use crate::runtime::v2::sumcheck;
    let f = Gf2_128Field::new();
    for leaves in [2, 3, 5, 8, 13] {
        let shape = TreeShape { trees: 2, leaves };
        let (npublic, start) = (3, 11);
        let c = fragment(npublic, start, shape).unwrap();
        assert_eq!(c.raw.ninput, start + 2 * leaves);
        assert_eq!(c.raw.noutput, 2);
        // Committed bits: 0/1 values at [npublic, start).
        let bits: Vec<_> = (0..start)
            .map(|i| f.u128_to_element((i % 2) as u128))
            .collect();
        let x = f.u128_to_element(7);
        let trees = (0..2)
            .map(|t| {
                let leaves: Vec<_> = (0..leaves)
                    .map(|i| Leaf::data(npublic + (i + t) % (start - npublic), x, &f))
                    .collect();
                // Honest target: the product of the leaf values.
                let target = leaves.iter().fold(f.one(), |acc, l| {
                    let v = f.addf(&l.constant, &f.mulf(&l.coefficient, &bits[l.source]));
                    f.mulf(&acc, &v)
                });
                TreeInstance { leaves, target }
            })
            .collect();
        let v = virtual_inputs(shape, trees, &f).unwrap();
        let mut inputs = bits.clone();
        for e in &v.entries {
            inputs.push(f.addf(&e.constant, &f.mulf(&e.coefficient, &bits[e.source])));
        }
        sumcheck::eval_circuit(inputs.clone(), &c, &f).unwrap();
        // Perturb one leaf: the product is no longer one.
        let mut bad = inputs.clone();
        bad[start] = f.addf(&bad[start], &f.one());
        assert!(sumcheck::eval_circuit(bad, &c, &f).is_err());
    }
}

#[test]
fn storage_runs_are_maximal_and_canonical() {
    use super::storage::{Coordinate, Group, Run};
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
    // A value stored as extension coordinates is its own run.
    let wide = Group {
        start: 0,
        width: 23,
    };
    let map = StorageMap::with_coordinates(2, &[(1, 0, wide), (1, 2, wide)]).unwrap();
    assert_eq!(
        map.runs(),
        [
            Run::Native {
                first: 0,
                count: 1,
                cell: 0
            },
            Run::Coordinates {
                value: 1,
                coordinates: vec![
                    Coordinate {
                        index: 0,
                        group: wide
                    },
                    Coordinate {
                        index: 2,
                        group: wide
                    }
                ]
            },
        ]
    );
}
