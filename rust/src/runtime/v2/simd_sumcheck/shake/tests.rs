// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    circuits::keccak::keccak_f_1600_trajectory,
    runtime::{
        algebra::gf2_128::Gf2_128 as E,
        random::{DeterministicRng, RandomEngine},
    },
};
#[test]
fn packed_keccak_matches_native_and_shares_each_endpoint_bit() {
    for count in [1, 129] {
        let mut rng = DeterministicRng::new(count as u64);
        let mut private = vec![];
        let mut links = vec![];
        for _ in 0..count {
            let state: [[u64; 5]; 5] =
                std::array::from_fn(|_| std::array::from_fn(|_| rng.u128() as u64));
            let final_state = keccak_f_1600_trajectory(state)[24];
            let start = private.len();
            for endpoint in [state, final_state] {
                for row in endpoint {
                    for lane in row {
                        private.extend((0..64).map(|r| lane >> r & 1 != 0));
                    }
                }
            }
            links.push((
                (start..start + 1600).collect(),
                (start + 1600..start + 3200).collect(),
            ));
        }
        private.extend([true, false, true]);
        let shared = SharedShake::new(private.len(), links).unwrap();
        let words = shared.witness(&private).unwrap();
        for (&v, &(word, bit)) in private.iter().zip(shared.placements()) {
            assert_eq!(v, words[word].to_u128() >> bit & 1 != 0);
        }
        let mut bad = private.clone();
        bad[0] ^= true;
        assert!(shared.witness(&bad).is_err());
        if count == 1 {
            let config = crate::runtime::v2::proto::polygero::PolygeroConfig {
                k: 349,
                s: 12,
                n: 2443,
                t: 84,
            };
            let proof = shared
                .program
                .prove_complete(words.clone(), b"Keccak permutation test", config, &mut rng)
                .unwrap();
            shared
                .program
                .verify_complete(&proof, b"Keccak permutation test", config)
                .unwrap();
            assert!(shared
                .program
                .verify_complete(&proof, b"wrong context", config)
                .is_err());
            let mut bad_words = words;
            bad_words[shared.scalar_words].xor_in_place(&E::from(1));
            assert!(shared
                .program
                .prove_complete(bad_words, b"Keccak permutation test", config, &mut rng)
                .is_err());
        }
    }
}
