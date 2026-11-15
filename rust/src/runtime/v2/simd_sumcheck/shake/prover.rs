// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::algebra::gf2_128::Gf2_128 as E;

impl SharedShake {
    pub fn witness(&self, private: &[bool]) -> Result<Vec<E>, String> {
        if private.len() != self.placements.len() {
            return Err("SIMD SHAKE private source length".into());
        }
        let mut words = vec![0u128; self.program.input_words()];
        for (&bit, &(word, lane)) in private.iter().zip(&self.placements) {
            words[word] |= (bit as u128) << lane;
        }
        for batch in 0..self.batches {
            let mut state = words[batch * 3200..batch * 3200 + 1600].to_vec();
            for (round, &round_constant) in ROUNDC.iter().enumerate() {
                let columns: Vec<_> = (0..320)
                    .map(|i| (0..5).fold(0, |sum, y| sum ^ state[at(i / 64, y, i % 64)]))
                    .collect();
                let mut b = vec![0; 1600];
                for x in 0..5 {
                    for y in 0..5 {
                        for z in 0..64 {
                            b[at(y, (2 * x + 3 * y) % 5, (z + ROTC[x][y]) % 64)] = state
                                [at(x, y, z)]
                                ^ columns[(x + 4) % 5 * 64 + z]
                                ^ columns[(x + 1) % 5 * 64 + (z + 63) % 64];
                        }
                    }
                }
                for x in 0..5 {
                    for y in 0..5 {
                        for z in 0..64 {
                            state[at(x, y, z)] = b[at(x, y, z)]
                                ^ (!b[at((x + 1) % 5, y, z)] & b[at((x + 2) % 5, y, z)]);
                            if x == 0 && y == 0 && round_constant >> z & 1 != 0 {
                                state[at(x, y, z)] ^= u128::MAX;
                            }
                        }
                    }
                }
                if round < 23 {
                    let start = self.scalar_words + batch * 23 * 1600 + round * 1600;
                    words[start..start + 1600].copy_from_slice(&state);
                }
            }
            let active = (self.links.len() - 128 * batch).min(128);
            let mask = u128::MAX >> (128 - active);
            for (j, &state_word) in state.iter().enumerate() {
                let end = batch * 3200 + 1600 + j;
                if (words[end] ^ state_word) & mask != 0 {
                    return Err("SHAKE permutation endpoint mismatch".into());
                }
                words[end] = state_word;
            }
        }
        Ok(words.into_iter().map(E::from).collect())
    }
}
