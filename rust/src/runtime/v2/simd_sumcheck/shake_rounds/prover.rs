// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{circuits::keccak::keccak_f_1600_trajectory, runtime::algebra::gf2_128::Gf2_128 as E};

impl SharedShakeRounds {
    pub fn witness(&self, private: &[bool]) -> Result<Vec<E>, String> {
        if private.len() != self.placements.len() {
            return Err("round-packed SHAKE witness length".into());
        }
        let mut words = vec![0u128; self.program.input_words()];
        for (&bit, &(word, lane)) in private.iter().zip(&self.placements) {
            words[word] |= u128::from(bit) << lane;
        }
        for (permutation, (initial, final_state)) in self.links.iter().enumerate() {
            let initial_state = std::array::from_fn(|x| {
                std::array::from_fn(|y| {
                    (0..64).fold(0u64, |word, z| {
                        word | (u64::from(private[initial[at(x, y, z)]])) << z
                    })
                })
            });
            let trajectory = keccak_f_1600_trajectory(initial_state);
            for (round, state) in trajectory.iter().skip(1).enumerate() {
                let index = permutation * 24 + round;
                let lane = index % 128;
                let base = index / 128 * 1600;
                for (x, column) in state.iter().enumerate() {
                    for (y, word) in column.iter().enumerate() {
                        for z in 0..64 {
                            let bit = (word >> z) & 1;
                            let position = at(x, y, z);
                            if round == 23 && private[final_state[position]] != (bit != 0) {
                                return Err("round-packed Keccak endpoint mismatch".into());
                            }
                            words[base + position] = (words[base + position] & !(1u128 << lane))
                                | (u128::from(bit) << lane);
                        }
                    }
                }
            }
        }
        Ok(words.into_iter().map(E::from).collect())
    }
}
