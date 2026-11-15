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

//! Native SampleInBall and its witness.

use super::{
    shake::{shake256_witness, ConcreteShake256Witness},
    Polynomial,
};
use crate::{
    core::algebra::fp24::Q,
    mldsa::proto::{BinaryKeccak, MlDsaParams, N, ROUTING_SIZE, SAMPLE_IN_BALL_BYTES},
    runtime::algebra::RuntimeField,
};

mod routing;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteSampleInBallWitness {
    pub shake: ConcreteShake256Witness,
    pub samples: Vec<u8>,
    pub sample_indices: Vec<u8>,
    pub position_trace: Vec<Vec<u8>>,
    pub selection_thresholds: Vec<u8>,
    pub selection_done: Vec<bool>,
    pub selection_switches: Vec<bool>,
    pub fill_positions: Vec<u8>,
    pub scatter_switches: Vec<bool>,
}

pub fn sample_in_ball<P: MlDsaParams>(
    seed: &[u8],
) -> Option<(Polynomial, ConcreteSampleInBallWitness)> {
    if seed.len() != P::C_TILDE_BYTES {
        return None;
    }
    let (hash, shake) = shake256_witness(seed, SAMPLE_IN_BALL_BYTES);
    let mut coefficients = [0u32; N];
    let mut samples = Vec::with_capacity(P::TAU);
    let mut sample_indices = Vec::with_capacity(P::TAU);
    let mut hash_index = 8;
    for i in N - P::TAU..N {
        let sample = loop {
            let value = *hash.get(hash_index)?;
            let index = hash_index;
            hash_index += 1;
            if usize::from(value) <= i {
                sample_indices.push(u8::try_from(index).ok()?);
                break value;
            }
        };
        samples.push(sample);
        coefficients[i] = coefficients[usize::from(sample)];
        coefficients[usize::from(sample)] =
            if (hash[(i + P::TAU - N) / 8] >> ((i + P::TAU - N) % 8)) & 1 == 1 {
                Q - 1
            } else {
                1
            };
    }

    let mut current_positions = Vec::with_capacity(P::TAU);
    let mut position_trace = Vec::with_capacity(P::TAU);
    for (step, &sample) in samples.iter().enumerate() {
        if let Some(position) = current_positions
            .iter_mut()
            .find(|position| **position == sample)
        {
            *position = (N - P::TAU + step) as u8;
        }
        current_positions.push(sample);
        position_trace.push(current_positions.clone());
    }
    let mut threshold = (N - P::TAU) as u8;
    let mut done = false;
    let mut selection_thresholds = vec![threshold];
    let mut selection_done = vec![done];
    for &byte in hash.iter().skip(8) {
        if !done && byte <= threshold {
            done = threshold == 255;
            threshold = threshold.wrapping_add(1);
        }
        selection_thresholds.push(threshold);
        selection_done.push(done);
    }
    assert!(done);
    let selected: Vec<_> = sample_indices.iter().map(|&i| usize::from(i) - 8).collect();
    let mut order = selected.clone();
    order.extend((0..ROUTING_SIZE).filter(|i| !selected.contains(i)));
    let mut selection_permutation = vec![0; ROUTING_SIZE];
    for (output, &input) in order.iter().enumerate() {
        selection_permutation[input] = output;
    }
    let selection_switches =
        routing::partial_switches(&selection_permutation, P::TAU, SAMPLE_IN_BALL_BYTES - 8);
    let fill_positions: Vec<_> = (0..N)
        .map(|i| i as u8)
        .filter(|i| !current_positions.contains(i))
        .collect();
    let scatter_permutation: Vec<_> = current_positions
        .iter()
        .chain(&fill_positions)
        .map(|&i| usize::from(i))
        .collect();
    let scatter_switches = routing::partial_switches(&scatter_permutation, N, N);
    Some((
        coefficients,
        ConcreteSampleInBallWitness {
            shake,
            samples,
            sample_indices,
            position_trace,
            selection_thresholds,
            selection_done,
            selection_switches,
            fill_positions,
            scatter_switches,
        },
    ))
}

impl ConcreteSampleInBallWitness {
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
        let bit_value = |bit| if bit { field.one() } else { field.zero() };
        destination.extend(self.prefix_bits().map(bit_value));
        self.shake
            .push_wires_with_keccak(field, destination, keccak);
        destination.extend(self.suffix_bits().map(bit_value));
    }
    fn prefix_bits(&self) -> impl Iterator<Item = bool> + '_ {
        self.samples
            .iter()
            .zip(&self.sample_indices)
            .flat_map(|(&sample, &index)| {
                [(u64::from(sample), 8), (u64::from(index), 8)]
                    .into_iter()
                    .flat_map(|(value, width)| (0..width).map(move |bit| value >> bit & 1 != 0))
            })
    }
    fn suffix_bits(&self) -> impl Iterator<Item = bool> + '_ {
        self.position_trace
            .iter()
            .flatten()
            .flat_map(|&value| (0..8).map(move |bit| value >> bit & 1 != 0))
            .chain(
                self.selection_thresholds
                    .iter()
                    .zip(&self.selection_done)
                    .flat_map(|(&value, &done)| {
                        (0..9).map(move |bit| {
                            if bit == 8 {
                                done
                            } else {
                                value >> bit & 1 != 0
                            }
                        })
                    }),
            )
            .chain(self.selection_switches.iter().copied())
            .chain(
                self.fill_positions
                    .iter()
                    .flat_map(|&value| (0..8).map(move |bit| value >> bit & 1 != 0)),
            )
            .chain(self.scatter_switches.iter().copied())
    }
}

cfg_prover! { mod prover; }
