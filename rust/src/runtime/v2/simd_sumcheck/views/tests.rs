// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::proto::v2::{Circuit, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    runtime::{
        random::{DeterministicRng, RandomEngine},
        v2::{proto::polygero::PolygeroConfig, simd_sumcheck::Program},
    },
};
fn circuit() -> Circuit<F> {
    let f = F::new();
    Circuit::from_raw(
        &f,
        RawCircuitBuilder {
            ninput: 5,
            npublic_input: 0,
            noutput: 1,
            logv: 0,
            constants: vec![f.one()],
            layers: vec![Layer::new(
                5,
                Stream::<Quadratic>::from_terms([Quadratic {
                    g: 0,
                    l: 3,
                    r: 1,
                    k: 0,
                }]),
                Stream::<Linear>::from_terms([
                    Linear { g: 0, l: 2, k: 0 },
                    Linear { g: 0, l: 4, k: 0 },
                ]),
                Stream::default(),
            )],
        }
        .build(),
    )
}
fn mapped(constants: [u128; 2], shift: usize) -> Program {
    let maps = vec![
        BitPermutation::identity(),
        BitPermutation::new(std::array::from_fn(|j| {
            j.checked_sub(shift).map(|i| i as u8)
        }))
        .unwrap(),
        BitPermutation::new(std::array::from_fn(|j| Some((127 - j) as u8))).unwrap(),
    ];
    let forms = vec![
        BitAffineInput {
            terms: vec![MappedTerm { word: 0, map: 1 }],
            constant: constants[0],
        },
        BitAffineInput {
            terms: vec![MappedTerm { word: 0, map: 2 }],
            constant: constants[1],
        },
    ];
    Program::new_with_bit_views(circuit(), 3, maps, forms, [79; 32]).unwrap()
}
#[test]
fn partial_maps_and_their_transposes_match_independent_bit_sums() {
    let mut rng = DeterministicRng::new(41);
    let f = F::new();
    for shift in [0, 1, 37, 127] {
        let map = BitPermutation::new(std::array::from_fn(|j| {
            j.checked_sub(shift).map(|i| i as u8)
        }))
        .unwrap();
        let input = rng.u128();
        assert_eq!(map.apply(input), input << shift);
        let lanes = std::array::from_fn(|_| E::from(rng.u128()));
        let pulled = map.transpose(&lanes);
        let mut expected = f.zero();
        let output = map.apply(input);
        let mut actual = f.zero();
        for j in 0..128 {
            if output >> j & 1 != 0 {
                expected.xor_in_place(&lanes[j]);
            }
            if input >> j & 1 != 0 {
                actual.xor_in_place(&pulled[j]);
            }
        }
        assert_eq!(actual, expected);
    }
    let mut duplicate = [None; 128];
    duplicate[0] = Some(3);
    duplicate[1] = Some(3);
    assert!(BitPermutation::new(duplicate).is_err());
    let mut invalid = [None; 128];
    invalid[0] = Some(128);
    assert!(BitPermutation::new(invalid).is_err());
}
#[test]
fn mapped_copies_and_lane_constants_are_authenticated() {
    let constants = [0xfedc9876543210u128, 0x10000000000200000000000000000004];
    let p = mapped(constants, 1);
    let a = 0x9234567890abdef123u128;
    let b = 0xfedcba9876543210u128;
    let words = vec![
        E::from(a),
        E::from(b),
        E::from(((a << 1) ^ constants[0]) & b ^ a.reverse_bits() ^ constants[1]),
    ];
    let config = PolygeroConfig {
        k: 64,
        s: 4,
        n: 448,
        t: 24,
    };
    let context = b"mapped packed bits";
    let mut rng = DeterministicRng::new(91);
    let proof = p
        .prove_complete(words.clone(), context, config, &mut rng)
        .unwrap();
    p.verify_complete(&proof, context, config).unwrap();
    assert_ne!(p.statement_id(), mapped(constants, 2).statement_id());
    assert!(mapped(constants, 2)
        .verify_complete(&proof, context, config)
        .is_err());
    assert!(mapped([constants[0] ^ 1, constants[1]], 1)
        .verify_complete(&proof, context, config)
        .is_err());
    assert!(mapped([constants[0], constants[1] ^ 1], 1)
        .verify_complete(&proof, context, config)
        .is_err());
    // Test the actual reconstructed authenticated equations against changed
    // committed source cells, independently of the witness residual checker.
    let (state, cells) = p.prepare(words, &mut rng).unwrap();
    let mut pt = p.start(context, config);
    let (reduction, rows) = p.prove(state, &mut pt.borrow()).unwrap();
    let mut vt = p.start(context, config);
    let replay = p.reduce(&reduction, &mut vt.borrow()).unwrap();
    assert!(rows
        .iter()
        .chain(&replay)
        .all(|row| row.evaluate(&cells).unwrap() == E::from(0)));
    for (word, bit) in [(0, 0), (0, 126), (2, 5)] {
        let mut altered = cells.clone();
        altered[word].xor_in_place(&E::from(1u128 << bit));
        assert!(
            replay
                .iter()
                .any(|row| row.evaluate(&altered).unwrap() != E::from(0)),
            "unauthenticated source bit {word}:{bit}"
        );
    }
}

#[test]
fn mapped_constructor_checks_indices_and_binds_even_unused_maps() {
    let baseline = mapped([7, 11], 1);
    let views = baseline.inputs.mapped().unwrap();
    let mut extra_maps = views.maps.clone();
    extra_maps.push(BitPermutation::new([None; 128]).unwrap());
    let extended =
        Program::new_with_bit_views(circuit(), 3, extra_maps, views.forms.clone(), [79; 32])
            .unwrap();
    assert_ne!(baseline.statement_id(), extended.statement_id());
    let mut invalid = views.forms.clone();
    invalid[0].terms[0].word = 3;
    assert!(
        Program::new_with_bit_views(circuit(), 3, views.maps.clone(), invalid, [79; 32]).is_err()
    );
    let mut invalid_map = views.forms.clone();
    invalid_map[0].terms[0].map = views.maps.len();
    assert!(
        Program::new_with_bit_views(circuit(), 3, views.maps.clone(), invalid_map, [79; 32])
            .is_err()
    );
    let mut no_identity = views.maps.clone();
    no_identity[0] = BitPermutation::new([None; 128]).unwrap();
    assert!(
        Program::new_with_bit_views(circuit(), 3, no_identity, views.forms.clone(), [79; 32])
            .is_err()
    );
}

#[test]
fn mapped_constant_only_relation_retains_its_source_dimension() {
    let f = F::new();
    let relation = Circuit::from_raw(
        &f,
        RawCircuitBuilder {
            ninput: 4,
            npublic_input: 0,
            noutput: 1,
            logv: 0,
            constants: vec![f.one()],
            layers: vec![Layer::new(
                4,
                Stream::<Quadratic>::from_terms([Quadratic {
                    g: 0,
                    l: 1,
                    r: 2,
                    k: 0,
                }]),
                Stream::<Linear>::from_terms([Linear { g: 0, l: 3, k: 0 }]),
                Stream::default(),
            )],
        }
        .build(),
    );
    let a = 0x123456789abcdefu128;
    let b = 0x9876543210u128;
    let forms = [a, b, a & b]
        .into_iter()
        .map(|constant| BitAffineInput {
            terms: Vec::new(),
            constant,
        })
        .collect();
    let program = Program::new_with_bit_views(
        relation,
        1,
        vec![BitPermutation::identity()],
        forms,
        [81; 32],
    )
    .unwrap();
    let config = PolygeroConfig {
        k: 64,
        s: 4,
        n: 448,
        t: 24,
    };
    let proof = program
        .prove_complete(
            vec![E::from(77)],
            b"constant bit views",
            config,
            &mut DeterministicRng::new(93),
        )
        .unwrap();
    program
        .verify_complete(&proof, b"constant bit views", config)
        .unwrap();
}
