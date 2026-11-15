// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::switches;
use crate::{
    mldsa::proto::{routing_plan, ROUTING_SIZE},
    runtime::random::{DeterministicRng, RandomEngine},
};
#[test]
fn every_native_route_matches_the_fixed_network() {
    let pairs = routing_plan(ROUTING_SIZE, ROUTING_SIZE).pairs;
    let mut rng = DeterministicRng::new(0x726f757465);
    for _ in 0..64 {
        let mut permutation: Vec<_> = (0..ROUTING_SIZE).collect();
        for i in (1..ROUTING_SIZE).rev() {
            let j = (rng.u128() % (i + 1) as u128) as usize;
            permutation.swap(i, j);
        }
        let controls = switches(&permutation);
        assert_eq!(controls.len(), pairs.len());
        let mut actual: Vec<_> = (0..ROUTING_SIZE).collect();
        for (&swap, &(a, b)) in controls.iter().zip(&pairs) {
            if swap {
                actual.swap(a, b);
            }
        }
        for (input, &output) in permutation.iter().enumerate() {
            assert_eq!(actual[output], input);
        }
    }
}

#[test]
fn pruning_preserves_each_observed_record_including_zero_padding() {
    use super::partial_switches;
    let mut rng = DeterministicRng::new(0x7072756e65);
    for outputs in [39, 49, 60] {
        for _ in 0..32 {
            let inputs = 213;
            let mut permutation: Vec<_> = (0..ROUTING_SIZE).collect();
            for i in (1..ROUTING_SIZE).rev() {
                let j = (rng.u128() % (i + 1) as u128) as usize;
                permutation.swap(i, j);
            }
            let source: Vec<_> = (0..ROUTING_SIZE)
                .map(|i| if i < inputs { i + 1 } else { 0 })
                .collect();
            let mut expected = vec![0; ROUTING_SIZE];
            for (input, &output) in permutation.iter().enumerate() {
                expected[output] = source[input];
            }
            let plan = routing_plan(outputs, inputs);
            let controls = partial_switches(&permutation, outputs, inputs);
            assert_eq!(controls.len(), plan.pairs.len());
            let mut actual = source;
            for (&swap, &(a, b)) in controls.iter().zip(&plan.pairs) {
                if swap {
                    actual.swap(a, b);
                }
            }
            assert_eq!(actual[..outputs], expected[..outputs]);
        }
    }
}
