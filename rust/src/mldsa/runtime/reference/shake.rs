// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Native SHAKE and witness construction.

use crate::{
    circuits::keccak::{keccak_f_1600_trajectory, ConcreteDerived},
    mldsa::proto::*,
    runtime::algebra::RuntimeField,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteShake256Witness {
    pub initial_states: Vec<[[u64; 5]; 5]>,
    pub permutations: Vec<ConcreteDerived>,
}

fn permute_native(state: &mut [[u64; 5]; 5], witness: &mut ConcreteShake256Witness) {
    witness.initial_states.push(*state);
    let trajectory = keccak_f_1600_trajectory(*state);
    witness.permutations.push(ConcreteDerived {
        // Keep the full trajectory so different trusted binary circuit
        // configurations can select their own committed checkpoints.
        intermediate_states: trajectory[1..=KECCAK_ROUNDS].to_vec(),
    });
    *state = trajectory[24];
}

fn xof_witness(input: &[u8], output_len: usize, rate: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    let mut padded = input.to_vec();
    let padding = rate - input.len() % rate;
    if padding == 1 {
        padded.push(0x9f);
    } else {
        padded.push(0x1f);
        padded.resize(padded.len() + padding - 2, 0);
        padded.push(0x80);
    }

    let mut state = [[0u64; 5]; 5];
    let mut witness = ConcreteShake256Witness {
        initial_states: Vec::new(),
        permutations: Vec::with_capacity(
            input.len() / rate + 1 + output_len.div_ceil(rate).saturating_sub(1),
        ),
    };
    for block in padded.chunks_exact(rate) {
        for (i, &byte) in block.iter().enumerate() {
            let lane = i / 8;
            state[lane % 5][lane / 5] ^= u64::from(byte) << (8 * (i % 8));
        }
        permute_native(&mut state, &mut witness);
    }

    let mut output = Vec::with_capacity(output_len);
    while output.len() < output_len {
        for i in 0..rate.min(output_len - output.len()) {
            let lane = i / 8;
            output.push((state[lane % 5][lane / 5] >> (8 * (i % 8))) as u8);
        }
        if output.len() < output_len {
            permute_native(&mut state, &mut witness);
        }
    }
    (output, witness)
}

pub fn shake256_witness(input: &[u8], output_len: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    xof_witness(input, output_len, SHAKE256_RATE)
}
pub fn shake128_witness(input: &[u8], output_len: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    xof_witness(input, output_len, 168)
}

#[must_use]
pub fn shake128(input: &[u8], output_len: usize) -> Vec<u8> {
    xof_witness(input, output_len, 168).0
}

impl ConcreteShake256Witness {
    pub fn push_wires<F: RuntimeField>(&self, field: &F, destination: &mut Vec<F::E>) {
        let keccak = if field.is_zero(&field.addf(&field.one(), &field.one())) {
            BinaryKeccak::default()
        } else {
            BinaryKeccak::legacy()
        };
        self.push_wires_with_keccak(field, destination, keccak);
    }

    pub fn push_wires_with_keccak<F: RuntimeField>(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
        keccak: BinaryKeccak,
    ) {
        let binary = field.is_zero(&field.addf(&field.one(), &field.one()));
        assert!(!keccak.external_permutations || binary);
        destination.extend(self.bits_with_keccak(keccak).map(|bit| {
            if binary {
                if bit {
                    field.one()
                } else {
                    field.zero()
                }
            } else if bit {
                field.mone()
            } else {
                field.one()
            }
        }));
    }

    /// Checked checkpoint bits in the same order as circuit allocation. Binary
    /// frontends can consume these directly without a temporary field vector.
    pub fn bits_with_keccak(&self, keccak: BinaryKeccak) -> impl Iterator<Item = bool> + '_ {
        keccak.validate();
        self.permutations
            .iter()
            .enumerate()
            .flat_map(move |(index, permutation)| {
                assert_eq!(permutation.intermediate_states.len(), KECCAK_ROUNDS);
                let initial = keccak
                    .external_permutations
                    .then(|| &self.initial_states[index])
                    .into_iter();
                let rounds = permutation
                    .intermediate_states
                    .iter()
                    .enumerate()
                    .filter_map(move |(round, state)| {
                        let keep = if keccak.external_permutations {
                            round + 1 == KECCAK_ROUNDS
                        } else {
                            keccak.checkpoint(round)
                        };
                        keep.then_some(state)
                    });
                initial.chain(rounds).flat_map(|state| {
                    state
                        .iter()
                        .flatten()
                        .flat_map(|&lane| (0..64).map(move |bit| lane >> bit & 1 != 0))
                })
            })
    }
}
