// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{prover::reduce, verifier::replay, *};
use crate::runtime::{
    random::{DeterministicRng, RandomEngine},
    v2::{
        proto::sumcheck::SumcheckProofGeometry,
        sumcheck::{bind, sample_pads_for_test},
        transcript::{Transcript, ZkStatement},
    },
};
#[test]
fn packed_rounds_match_expanded_field_tables_and_replay() {
    let f = F::new();
    let mut rng = DeterministicRng::new(129);
    for count in [1, 3, 17, 128] {
        let words: Vec<_> = (0..11).map(|_| rng.elt_field(&f)).collect();
        let weights: Vec<_> = (0..5).map(|_| rng.elt_field(&f)).collect();
        let products: Vec<_> = (0..count)
            .map(|i| Product {
                g: i % 5,
                l: i % 11,
                r: (3 * i + 2) % 11,
            })
            .collect();
        let (all_pads, _) = sample_pads_for_test(
            &SumcheckProofGeometry::new(vec![rounds(count).unwrap()]).unwrap(),
            &mut rng,
            &f,
        );
        let pads = &all_pads.layers[0];
        let mut t = Transcript::new(&ZkStatement {
            context: b"simd-kernel-test",
        });
        let reduced = reduce(&products, &words, &weights, pads, &mut t.borrow()).unwrap();
        let mut tv = Transcript::new(&ZkStatement {
            context: b"simd-kernel-test",
        });
        assert_eq!(
            replay(count, &reduced.messages, &mut tv.borrow()).unwrap(),
            reduced.challenges
        );
        let mut x = Vec::new();
        let mut y = Vec::new();
        for p in &products {
            for lane in 0..128 {
                x.push(E::from(words[p.l].to_u128() >> lane & 1));
                y.push(f.mulf(
                    &weights[p.g],
                    &E::from((words[p.r].to_u128() >> lane & 1) << lane),
                ));
            }
        }
        let mut claim = crate::runtime::algebra::blas::dot(&x, &y, &f);
        for (i, z) in reduced.challenges.point.iter().enumerate() {
            let poly = packed::quad_round_poly(&y, &x, &claim, &f);
            for j in 0..2 {
                assert_eq!(
                    f.addf(
                        &reduced.messages.rounds[i].coefficients[j],
                        &pads.rounds[i].coefficients[j]
                    ),
                    poly.coefficients[j]
                );
            }
            bind(&mut x, z, &f);
            bind(&mut y, z, &f);
            // The next round's incoming claim is the complete remaining dot.
            claim = crate::runtime::algebra::blas::dot(&x, &y, &f);
        }
        let r = reduced.challenges.terminal;
        assert_eq!(
            reduced.messages.claims,
            [
                f.addf(&x[0], &f.mulf(&r, &pads.claims[0])),
                f.addf(&y[0], &f.mulf(&r, &pads.claims[1]))
            ]
        );
    }
}
