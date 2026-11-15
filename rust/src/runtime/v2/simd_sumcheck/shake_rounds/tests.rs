// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    circuits::keccak::keccak_f_1600_trajectory,
    runtime::{
        algebra::gf2_128::Gf2_128 as E,
        random::{DeterministicRng, RandomEngine},
        v2::proto::polygero::PolygeroConfig,
    },
};
fn instance(count: usize) -> (Vec<bool>, Vec<(Vec<usize>, Vec<usize>)>) {
    let mut rng = DeterministicRng::new(count as u64 + 400);
    let mut private = Vec::new();
    let mut links = Vec::new();
    for _ in 0..count {
        let initial = std::array::from_fn(|_| std::array::from_fn(|_| rng.u128() as u64));
        let end = keccak_f_1600_trajectory(initial)[24];
        let start = private.len();
        for state in [initial, end] {
            for column in state {
                for word in column {
                    private.extend((0..64).map(|bit| word >> bit & 1 != 0));
                }
            }
        }
        links.push((
            (start..start + 1600).collect(),
            (start + 1600..start + 3200).collect(),
        ));
    }
    private.extend((0..70_000).map(|bit| bit % 3 == 0));
    (private, links)
}
#[test]
fn round_batches_match_keccak_and_preserve_every_scalar_placement() {
    for count in [1, 9, 128, 129] {
        let (private, links) = instance(count);
        let source = SharedShakeRounds::new(private.len(), links).unwrap();
        let words = source.witness(&private).unwrap();
        assert_eq!(source.program.products(), (count * 24).div_ceil(128) * 1600);
        for (&value, &(word, lane)) in private.iter().zip(source.placements()) {
            assert_eq!(words[word].to_u128() >> lane & 1 != 0, value);
        }
        let mut altered = private.clone();
        altered[1600] ^= true;
        assert!(source.witness(&altered).is_err());
        if count == 9 {
            assert_eq!(source.program.input_words(), 4800);
            assert!(source.placements()[count * 3200].1 >= 88);
            assert_eq!(source.placements()[count * 3200 + 64_000], (3200, 9));
        }
    }
}
#[test]
fn cross_batch_predecessors_and_round_constants_are_authenticated() {
    let (private, links) = instance(9);
    let source = SharedShakeRounds::new(private.len(), links).unwrap();
    let words = source.witness(&private).unwrap();
    let config = PolygeroConfig {
        k: 349,
        s: 12,
        n: 2443,
        t: 84,
    };
    let context = b"round-packed Keccak authentication";
    let mut rng = DeterministicRng::new(100);
    let proof = source
        .program
        .prove_complete(words.clone(), context, config, &mut rng)
        .unwrap();
    source
        .program
        .verify_complete(&proof, context, config)
        .unwrap();
    let (state, cells) = source.program.prepare(words, &mut rng).unwrap();
    let mut pt = source.program.start(context, config);
    let (reduction, _) = source.program.prove(state, &mut pt.borrow()).unwrap();
    let mut vt = source.program.start(context, config);
    let rows = source.program.reduce(&reduction, &mut vt.borrow()).unwrap();
    assert!(rows
        .iter()
        .all(|row| row.evaluate(&cells).unwrap() == E::from(0)));
    // Global round127 is the predecessor of round128 in the next SIMD
    // batch. These checks authenticate that shifted source, not merely the
    // prover's honest witness-construction or residual checks.
    for (word, lane) in [(0, 127), (1600, 0), (3200, 5)] {
        let mut changed = cells.clone();
        changed[word].xor_in_place(&E::from(1u128 << lane));
        assert!(
            rows.iter()
                .any(|row| row.evaluate(&changed).unwrap() != E::from(0)),
            "unbound round source {word}:{lane}"
        );
    }
    for index in [40, proof.len() / 2, proof.len() - 1] {
        let mut changed = proof.clone();
        changed[index] ^= 1;
        assert!(source
            .program
            .verify_complete(&changed, context, config)
            .is_err());
    }
}

#[cfg(feature = "mldsa")]
#[test]
fn scalar_claim_authenticates_unused_round_and_start_lanes() {
    use crate::runtime::v2::simd_sumcheck::{shared::ScalarClaim, NativeRow};
    let (private, links) = instance(9);
    let source = SharedShakeRounds::new(private.len(), links).unwrap();
    let words = source.witness(&private).unwrap();
    let indices = [9 * 3200, 9 * 3200 + 64_002];
    let coefficients = [E::from(7), E::from(11)];
    let mut weights = vec![E::from(0); private.len()];
    let mut target = E::from(0);
    for (index, coefficient) in indices.into_iter().zip(coefficients) {
        weights[index] = coefficient;
        if private[index] {
            target.xor_in_place(&coefficient);
        }
    }
    let mask = E::from(54321);
    let scalar = || ScalarClaim {
        weights: weights.clone(),
        rhs: NativeRow {
            constant: F::new().addf(&target, &mask),
            terms: vec![(source.program.cell_count(), E::from(1))],
        },
    };
    let mut rng = DeterministicRng::new(101);
    let (state, cells) = source
        .program
        .prepare_shared(words, vec![mask], &mut rng)
        .unwrap();
    let mut pt = source.program.start(
        b"reused scalar lanes",
        PolygeroConfig {
            k: 349,
            s: 12,
            n: 2443,
            t: 84,
        },
    );
    let (proof, packing, _) = source
        .program
        .prove_shared(state, scalar(), source.placements(), &mut pt.borrow())
        .unwrap();
    let mut vt = source.program.start(
        b"reused scalar lanes",
        PolygeroConfig {
            k: 349,
            s: 12,
            n: 2443,
            t: 84,
        },
    );
    let rows = source
        .program
        .reduce_shared(
            &proof,
            &packing,
            scalar(),
            source.placements(),
            cells.len(),
            &mut vt.borrow(),
        )
        .unwrap();
    assert!(rows
        .iter()
        .all(|row| row.evaluate(&cells).unwrap() == E::from(0)));
    for index in indices {
        let (word, lane) = source.placements()[index];
        let mut changed = cells.clone();
        changed[word].xor_in_place(&E::from(1u128 << lane));
        assert!(
            rows.iter()
                .any(|row| row.evaluate(&changed).unwrap() != E::from(0)),
            "unbound reused scalar bit {index}"
        );
    }
}
