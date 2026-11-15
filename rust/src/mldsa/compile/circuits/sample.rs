// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact bounded SampleInBall through a rejection scan and packed-record routes.
use super::shake::{
    allocate_witness_with_keccak as allocate_shake_witness, Shake256, Shake256Witness,
};
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::{Bitvec, BitvecIO, BitvecLogic, V8},
        boolean::{Bitw, Boolean, BooleanIO},
    },
    compile::logic::{Eltw, Logic, LogicIO},
    core::algebra::SupportsU64Conversions,
    mldsa::proto::{
        routing_plan, BinaryKeccak, MlDsaParams, RoutingPlan, N, ROUTING_SIZE, SAMPLE_IN_BALL_BYTES,
    },
};
#[cfg(test)]
mod tests;

pub(crate) struct SampleInBallWitness<L: Logic> {
    pub shake: Shake256Witness<L>,
    pub samples: Vec<V8<L>>,
    pub sample_indices: Vec<V8<L>>,
    pub position_trace: Vec<Vec<V8<L>>>,
    pub selection_thresholds: Vec<V8<L>>,
    pub selection_done: Vec<Bitw<L>>,
    pub selection_switches: Vec<Bitw<L>>,
    pub fill_positions: Vec<V8<L>>,
    pub scatter_switches: Vec<Bitw<L>>,
}
pub(crate) fn allocate_witness_with_keccak<L: LogicIO, P: MlDsaParams>(
    bitvec: &BitvecLogic<L>,
    position: &mut usize,
    keccak: BinaryKeccak,
) -> SampleInBallWitness<L> {
    let io = BitvecIO::new(bitvec);
    let bits = BooleanIO::new(bitvec.logic());
    let mut samples = Vec::with_capacity(P::TAU);
    let mut sample_indices = Vec::with_capacity(P::TAU);
    for _ in 0..P::TAU {
        samples.push(io.next(position));
        sample_indices.push(io.next(position));
    }
    let shake = allocate_shake_witness(
        bitvec,
        position,
        P::C_TILDE_BYTES,
        SAMPLE_IN_BALL_BYTES,
        keccak,
    );
    let position_trace = (0..P::TAU)
        .map(|step| (0..=step).map(|_| io.next(position)).collect())
        .collect();
    let mut selection_thresholds = Vec::new();
    let mut selection_done = Vec::new();
    for _ in 0..=SAMPLE_IN_BALL_BYTES - 8 {
        selection_thresholds.push(io.next(position));
        selection_done.push(bits.next(position));
    }
    let switches = routing_plan(P::TAU, SAMPLE_IN_BALL_BYTES - 8).control_count();
    let selection_switches = (0..switches).map(|_| bits.next(position)).collect();
    let fill_positions = (P::TAU..N).map(|_| io.next(position)).collect();
    let scatter_switches = (0..routing_plan(N, N).control_count())
        .map(|_| bits.next(position))
        .collect();
    SampleInBallWitness {
        shake,
        samples,
        sample_indices,
        position_trace,
        selection_thresholds,
        selection_done,
        selection_switches,
        fill_positions,
        scatter_switches,
    }
}
/// A conditional swap of a whole encoded record costs one multiplication.
/// All selectors are Boolean inputs. Packing is injective through the field's
/// checked pseudo-basis, so the network is an exact permutation of records.
fn route<L: Logic>(
    logic: &L,
    mut records: Vec<Eltw<L>>,
    switches: &[Bitw<L>],
    outputs: usize,
    inputs: usize,
) -> Vec<Eltw<L>> {
    assert_eq!(records.len(), ROUTING_SIZE);
    let plan: RoutingPlan = routing_plan(outputs, inputs);
    let pairs = plan.pairs;
    assert_eq!(pairs.len(), switches.len());
    let boolean = Boolean::new(logic);
    let mut depths = [0usize; ROUTING_SIZE];
    for (&(a, b), selector) in pairs.iter().zip(switches) {
        let depth = 1 + depths[a].max(depths[b]);
        depths[a] = depth;
        depths[b] = depth;
        let delta = logic.mul(
            &boolean.as_eltw(selector),
            &logic.sub(&records[b], &records[a]),
        );
        let left = logic.add(&records[a], &delta);
        let right = logic.sub(&records[b], &delta);
        // One affine routing stage may feed the next quadratic switch. Cut
        // every second stage to bound expression growth without an extra
        // materialization layer after every switch.
        if depth % 2 == 0 {
            records[a] = logic.precious(&left);
            records[b] = logic.precious(&right);
        } else {
            records[a] = left;
            records[b] = right;
        }
    }
    records
}
fn selected_record<L: Logic>(
    logic: &L,
    value: &V8<L>,
    index: &V8<L>,
    selected: &Bitw<L>,
) -> Eltw<L> {
    let mut bits = value.as_array().to_vec();
    bits.extend_from_slice(index.as_array());
    bits.push(selected.clone());
    Arithmetic::new(logic).as_eltw_field(&bits)
}
fn signed_record<L: Logic>(
    logic: &L,
    index: &V8<L>,
    positive: &Bitw<L>,
    negative: &Bitw<L>,
) -> Eltw<L> {
    let mut bits = index.as_array().to_vec();
    bits.extend([positive.clone(), negative.clone()]);
    Arithmetic::new(logic).as_eltw_field(&bits)
}
fn assert_sample_selection<L: Logic, P: MlDsaParams>(
    logic: &L,
    hash: &[V8<L>],
    witness: &SampleInBallWitness<L>,
) -> Vec<L::Assertions> {
    const {
        assert!(SAMPLE_IN_BALL_BYTES < 256);
    }
    assert_eq!(hash.len(), SAMPLE_IN_BALL_BYTES);
    assert_eq!(
        witness.selection_thresholds.len(),
        SAMPLE_IN_BALL_BYTES - 8 + 1
    );
    assert_eq!(
        witness.selection_done.len(),
        witness.selection_thresholds.len()
    );
    let bitvec = BitvecLogic::new(logic);
    let boolean = Boolean::new(logic);
    let mut assertions = Vec::new();
    assertions.push(bitvec.assert_eq(
        "selection_initial_threshold",
        &witness.selection_thresholds[0],
        &bitvec.of_u64((N - P::TAU) as u64),
    ));
    assertions.push(boolean.assert_false("selection_initial_done", &witness.selection_done[0]));
    let mut records = Vec::with_capacity(ROUTING_SIZE);
    for (index, byte) in hash.iter().enumerate().skip(8) {
        let step = index - 8;
        let threshold = &witness.selection_thresholds[step];
        let done = &witness.selection_done[step];
        let selected =
            boolean.precious(&boolean.andb(&boolean.notb(done), &bitvec.leq(byte, threshold)));
        let mut increment = vec![boolean.falseb(); 8];
        increment[0] = selected.clone();
        assertions.push(bitvec.assert_wrapping_add(
            &witness.selection_thresholds[step + 1],
            threshold,
            &Bitvec::new(increment),
        ));
        let last = bitvec.eqb(threshold, &bitvec.of_u64(255));
        let finished = boolean.or_assuming_at_most_one_true(done, &boolean.andb(&selected, &last));
        assertions.push(boolean.assert_eq(
            "selection_done_step",
            &witness.selection_done[step + 1],
            &finished,
        ));
        records.push(selected_record(
            logic,
            byte,
            &bitvec.of_u64(index as u64),
            &selected,
        ));
    }
    assertions
        .push(boolean.assert_true("selection_complete", witness.selection_done.last().unwrap()));
    records.resize_with(ROUTING_SIZE, || logic.zero());
    let routed = route(
        logic,
        records,
        &witness.selection_switches,
        P::TAU,
        SAMPLE_IN_BALL_BYTES - 8,
    );
    let mut previous = bitvec.of_u64(8);
    for (step, record) in routed.iter().take(P::TAU).enumerate() {
        let index = &witness.sample_indices[step];
        assertions.push(boolean.assert_true("sample_index_order", &bitvec.leq(&previous, index)));
        assertions.push(boolean.assert_true(
            "sample_index_bound",
            &bitvec.leq(index, &bitvec.of_u64((SAMPLE_IN_BALL_BYTES - 1) as u64)),
        ));
        assertions.push(logic.assert_eq(
            "selected_record",
            record,
            &selected_record(logic, &witness.samples[step], index, &boolean.trueb()),
        ));
        previous = V8::new(
            Arithmetic::new(logic)
                .unchecked_add(index.as_array(), bitvec.of_u64::<8>(1).as_array())
                .0,
        );
    }
    assertions
}
fn assert_position_trace<L: Logic, P: MlDsaParams>(
    logic: &L,
    witness: &SampleInBallWitness<L>,
) -> Vec<L::Assertions> {
    let bitvec = BitvecLogic::new(logic);
    let boolean = Boolean::new(logic);
    let mut assertions = Vec::new();
    assertions.push(logic.assert_eq(
        "trace_initial",
        &bitvec.as_eltw_field(&witness.position_trace[0][0]),
        &bitvec.as_eltw_field(&witness.samples[0]),
    ));
    for step in 1..P::TAU {
        let previous = &witness.position_trace[step - 1];
        let current = &witness.position_trace[step];
        assertions.push(logic.assert_eq(
            "trace_append",
            &bitvec.as_eltw_field(&current[step]),
            &bitvec.as_eltw_field(&witness.samples[step]),
        ));
        for i in 0..step {
            let matches = bitvec.eqb(&previous[i], &witness.samples[step]);
            let old = bitvec.as_eltw_field(&previous[i]);
            let limit = bitvec.as_eltw_field(&bitvec.of_u64::<8>((N - P::TAU + step) as u64));
            let updated = logic.add(
                &old,
                &logic.mul(&boolean.as_eltw(&matches), &logic.sub(&limit, &old)),
            );
            assertions.push(logic.assert_eq(
                "trace_update",
                &bitvec.as_eltw_field(&current[i]),
                &updated,
            ));
        }
    }
    assertions
}
/// Check the challenge's positive and negative indicator bits directly. The
/// final route sends each signed token to its checked coordinate; zero tokens
/// fill the other positions. Output tags 0..255 enforce uniqueness as well.
pub(crate) fn assert_sample_in_ball_bits<L, P>(
    logic: &L,
    seed: &[V8<L>],
    witness: &SampleInBallWitness<L>,
    positive: &[Bitw<L>],
    negative: &[Bitw<L>],
) -> L::Assertions
where
    L: Logic,
    L::F: SupportsU64Conversions,
    P: MlDsaParams,
{
    assert_eq!(seed.len(), P::C_TILDE_BYTES);
    assert_eq!(positive.len(), N);
    assert_eq!(negative.len(), N);
    let bitvec = BitvecLogic::new(logic);
    let boolean = Boolean::new(logic);
    let shake = Shake256::with_keccak(logic, witness.shake.keccak);
    let (hash, valid_hash) = shake.assert_hash(seed, SAMPLE_IN_BALL_BYTES, &witness.shake);
    let mut assertions = vec![valid_hash];
    assertions.extend(assert_sample_selection::<_, P>(logic, &hash, witness));
    assertions.extend(assert_position_trace::<_, P>(logic, witness));
    let final_positions = &witness.position_trace[P::TAU - 1];
    let mut records = Vec::with_capacity(N);
    for (step, index) in final_positions.iter().enumerate() {
        let sign = hash[step / 8].bit(step % 8);
        records.push(signed_record(logic, index, &boolean.notb(sign), sign));
    }
    for index in &witness.fill_positions {
        records.push(signed_record(
            logic,
            index,
            &boolean.falseb(),
            &boolean.falseb(),
        ));
    }
    let scattered = route(logic, records, &witness.scatter_switches, N, N);
    for i in 0..N {
        assertions.push(logic.assert_eq(
            "scatter_record",
            &scattered[i],
            &signed_record(logic, &bitvec.of_u64(i as u64), &positive[i], &negative[i]),
        ));
    }
    logic.assert_all("sample_in_ball_trace", &assertions)
}
