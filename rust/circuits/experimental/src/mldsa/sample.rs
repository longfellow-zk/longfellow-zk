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

//! FIPS 204 `SampleInBall` witness construction and constraints.

use circuits_bitvec::{Bitvec, BitvecIO, BitvecLogic, V8};
use circuits_boolean::Boolean;
use compile_logic::{Logic, LogicIO};
use core_algebra::SupportsU64Conversions;

use super::{
    algebra::Q,
    circuit::PolynomialW,
    params::{MlDsaParams, N},
    reference::Polynomial,
    shake::{
        allocate_witness as allocate_shake_witness, shake256_witness, ConcreteShake256Witness,
        Shake256, Shake256Witness,
    },
};

type V16<L> = Bitvec<L, 16>;

pub struct SampleInBallWitness<L: Logic> {
    pub shake: Shake256Witness<L>,
    pub samples: Vec<V8<L>>,
    pub sample_indices: Vec<V16<L>>,
    pub position_trace: Vec<Vec<V8<L>>>,
}

pub fn allocate_witness<L: LogicIO, P: MlDsaParams>(
    bitvec: &BitvecLogic<L>,
    position: &mut usize,
) -> SampleInBallWitness<L> {
    let bitvec_io = BitvecIO::new(bitvec);
    let mut samples = Vec::with_capacity(P::TAU);
    let mut sample_indices = Vec::with_capacity(P::TAU);
    for _ in 0..P::TAU {
        samples.push(bitvec_io.next(position));
        sample_indices.push(bitvec_io.next(position));
    }
    let shake = allocate_shake_witness(bitvec, position, P::C_TILDE_BYTES, 136);
    let position_trace = (0..P::TAU)
        .map(|step| (0..=step).map(|_| bitvec_io.next(position)).collect())
        .collect();
    SampleInBallWitness {
        shake,
        samples,
        sample_indices,
        position_trace,
    }
}

pub fn assert_sample_in_ball<L, P>(
    logic: &L,
    seed: &[V8<L>],
    expected: &PolynomialW<L>,
    witness: &SampleInBallWitness<L>,
) -> L::Assertions
where
    L: Logic,
    L::F: SupportsU64Conversions,
    P: MlDsaParams,
{
    assert_eq!(seed.len(), P::C_TILDE_BYTES);
    assert_eq!(witness.samples.len(), P::TAU);
    assert_eq!(witness.sample_indices.len(), P::TAU);
    let bitvec = BitvecLogic::new(logic);
    let boolean = Boolean::new(logic);
    let shake = Shake256::new(logic);
    let (hash, hash_assertions) = shake.assert_hash(seed, 136, &witness.shake);
    let mut assertions = vec![hash_assertions];

    let mut previous_index: V16<L> = bitvec.of_u64(8);
    for step in 0..P::TAU {
        let limit = N - P::TAU + step;
        let sample = &witness.samples[step];
        let sample_index = &witness.sample_indices[step];
        assertions.push(boolean.assert_true(
            "sample_index_bound",
            &bitvec.leq(sample_index, &bitvec.of_u64(135)),
        ));
        assertions.push(boolean.assert_true(
            "sample_index_order",
            &bitvec.leq(&previous_index, sample_index),
        ));
        let sample_extended: V16<L> = bitvec.zext(sample);
        let limit_bits: V16<L> = bitvec.of_u64(limit as u64);
        assertions
            .push(boolean.assert_true("sample_bound", &bitvec.leq(&sample_extended, &limit_bits)));

        for (index, hash_byte) in hash.iter().enumerate() {
            let current: V16<L> = bitvec.of_u64(index as u64);
            let is_target = bitvec.eqb(&current, sample_index);
            let value_matches = bitvec.eqb(hash_byte, sample);
            assertions.push(boolean.assert_true(
                "sample_matches_hash",
                &boolean.impliesb(&is_target, &value_matches),
            ));
            let in_rejected_range = boolean.andb(
                &bitvec.leq(&previous_index, &current),
                &bitvec.lt(&current, sample_index),
            );
            let hash_extended: V16<L> = bitvec.zext(hash_byte);
            let was_rejected = bitvec.lt(&limit_bits, &hash_extended);
            assertions.push(boolean.assert_true(
                "rejection_is_valid",
                &boolean.impliesb(&in_rejected_range, &was_rejected),
            ));
        }
        previous_index = bitvec.wrapping_add(sample_index, &bitvec.of_u64(1));
    }

    assertions.push(bitvec.assert_eq(
        "trace_initial",
        &witness.position_trace[0][0],
        &witness.samples[0],
    ));
    for step in 1..P::TAU {
        let previous = &witness.position_trace[step - 1];
        let current = &witness.position_trace[step];
        assertions.push(bitvec.assert_eq("trace_append", &current[step], &witness.samples[step]));
        for i in 0..step {
            let matches = bitvec.eqb(&previous[i], &witness.samples[step]);
            let updated = bitvec.select(
                &matches,
                &bitvec.of_u64((N - P::TAU + step) as u64),
                &previous[i],
            );
            assertions.push(bitvec.assert_eq("trace_update", &current[i], &updated));
        }
    }

    let one = logic.one();
    let two = logic.add(&one, &one);
    let final_positions = &witness.position_trace[P::TAU - 1];
    let signs: Vec<_> = (0..P::TAU)
        .map(|step| {
            let sign = boolean.as_eltw(hash[step / 8].bit(step % 8));
            logic.sub(&one, &logic.mul(&two, &sign))
        })
        .collect();
    for coefficient in 0..N {
        let coefficient_bits: V8<L> = bitvec.of_u64(coefficient as u64);
        let terms: Vec<_> = final_positions
            .iter()
            .zip(&signs)
            .map(|(position, sign)| {
                let matches = boolean.as_eltw(&bitvec.eqb(position, &coefficient_bits));
                logic.mul(&matches, sign)
            })
            .collect();
        assertions.push(logic.assert_eq(
            "challenge_coefficient",
            &expected.coefficients[coefficient],
            &logic.sum(&terms),
        ));
    }
    logic.assert_all("sample_in_ball", &assertions)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteSampleInBallWitness {
    pub shake: ConcreteShake256Witness,
    pub samples: Vec<u8>,
    pub sample_indices: Vec<u16>,
    pub position_trace: Vec<Vec<u8>>,
}

pub fn sample_in_ball<P: MlDsaParams>(
    seed: &[u8],
) -> Option<(Polynomial, ConcreteSampleInBallWitness)> {
    if seed.len() != P::C_TILDE_BYTES {
        return None;
    }
    let (hash, shake) = shake256_witness(seed, 136);
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
                sample_indices.push(index as u16);
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
    Some((
        coefficients,
        ConcreteSampleInBallWitness {
            shake,
            samples,
            sample_indices,
            position_trace,
        },
    ))
}

#[cfg(feature = "mldsa-runtime")]
impl ConcreteSampleInBallWitness {
    pub fn push_wires<
        const W: usize,
        F: runtime_algebra::RuntimeField<W> + core_algebra::HasLookupPoints,
    >(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        for (&sample, &index) in self.samples.iter().zip(&self.sample_indices) {
            circuits_bitvec::concrete::push_bitvec_u64(field, u64::from(sample), 8, destination);
            circuits_bitvec::concrete::push_bitvec_u64(field, u64::from(index), 16, destination);
        }
        self.shake.push_wires(field, destination);
        for trace in &self.position_trace {
            for &position in trace {
                circuits_bitvec::concrete::push_bitvec_u64(
                    field,
                    u64::from(position),
                    8,
                    destination,
                );
            }
        }
    }
}
