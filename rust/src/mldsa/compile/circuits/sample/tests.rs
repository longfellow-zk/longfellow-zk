// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    compile::{
        algebra::gf2_128::Gf2_128Field as CF,
        compiler::{compile_v2, segment_circuit_v2},
        logic::K_FIRST_WIRE_POSITION,
    },
    core::{
        algebra::AlgebraicField,
        proto::v2::{CircuitReader, CircuitWriter},
    },
    mldsa::{
        proto::{MlDsa44, MlDsa65},
        runtime::reference::{sample_in_ball, ConcreteSampleInBallWitness},
    },
    runtime::{algebra::gf2_128::Gf2_128Field as RF, v2::sumcheck::eval_circuit},
};
fn exercise<P: MlDsaParams>() {
    let cf = CF::new();
    let (raw, _, _) = compile_v2(&cf, |l| {
        let bitvec = BitvecLogic::new(&l);
        let io = BitvecIO::new(&bitvec);
        let bit_io = BooleanIO::new(&l);
        let mut pos = K_FIRST_WIRE_POSITION;
        let positive: Vec<_> = (0..N).map(|_| bit_io.next(&mut pos)).collect();
        let negative: Vec<_> = (0..N).map(|_| bit_io.next(&mut pos)).collect();
        let seed: Vec<_> = (0..P::C_TILDE_BYTES).map(|_| io.next(&mut pos)).collect();
        let witness =
            allocate_witness_with_keccak::<_, P>(&bitvec, &mut pos, BinaryKeccak::default());
        (
            assert_sample_in_ball_bits::<_, P>(&l, &seed, &witness, &positive, &negative),
            K_FIRST_WIRE_POSITION,
        )
    });
    let compiled = segment_circuit_v2(&cf, raw);
    let bytes = CircuitWriter::new(&cf).to_bytes(&compiled);
    let rf = RF::new();
    let (circuit, tail) = CircuitReader::new(&rf).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    let seed = vec![37; P::C_TILDE_BYTES];
    let (c, w) = sample_in_ball::<P>(&seed).unwrap();
    let field = &rf;
    let inputs = |witness: &ConcreteSampleInBallWitness, challenge: &[u32; N]| {
        let mut values: Vec<_> = challenge
            .iter()
            .map(|&x| if x == 1 { field.one() } else { field.zero() })
            .chain(challenge.iter().map(|&x| {
                if x == crate::core::algebra::fp24::Q - 1 {
                    field.one()
                } else {
                    field.zero()
                }
            }))
            .collect();
        values.extend(seed.iter().flat_map(|&x| {
            (0..8).map(move |bit| {
                if x >> bit & 1 != 0 {
                    field.one()
                } else {
                    field.zero()
                }
            })
        }));
        witness.push_wires_with_keccak(field, &mut values, BinaryKeccak::default());
        values
    };
    eval_circuit(inputs(&w, &c), &circuit, &rf).unwrap();
    let reject = |bad: &ConcreteSampleInBallWitness| {
        assert!(eval_circuit(inputs(bad, &c), &circuit, &rf).is_err())
    };
    for index in [0, 7, 221, 255] {
        let mut bad = w.clone();
        bad.sample_indices[0] = index;
        reject(&bad);
    }
    let mut wrong_threshold = w.clone();
    wrong_threshold.selection_thresholds[1] ^= 1;
    reject(&wrong_threshold);
    let mut premature_done = w.clone();
    premature_done.selection_done[1] = true;
    reject(&premature_done);
    let mut wrong_sample = w.clone();
    wrong_sample.samples[0] ^= 1;
    reject(&wrong_sample);
    let mut wrong_position = w.clone();
    wrong_position.position_trace[P::TAU - 1][0] ^= 1;
    reject(&wrong_position);
    let mut wrong_fill = w.clone();
    wrong_fill.fill_positions[0] = w.position_trace[P::TAU - 1][0];
    reject(&wrong_fill);
    let mut changed = c;
    let nonzero = changed.iter().position(|&x| x != 0).unwrap();
    changed[nonzero] = 0;
    assert!(eval_circuit(inputs(&w, &changed), &circuit, &rf).is_err());
    // Flip a routing switch that actually changes the selected/scattered data.
    for which in 0..2 {
        let mut saw_rejected = false;
        for i in (0..w.selection_switches.len()).step_by(17) {
            let mut wrong_route = w.clone();
            let switches = if which == 0 {
                &mut wrong_route.selection_switches
            } else {
                &mut wrong_route.scatter_switches
            };
            switches[i] = !switches[i];
            if eval_circuit(inputs(&wrong_route, &c), &circuit, &rf).is_err() {
                saw_rejected = true;
                break;
            }
        }
        assert!(saw_rejected);
    }
}
#[test]
fn packed_records_match_mldsa44_and_reject_tampering() {
    exercise::<MlDsa44>();
}
#[test]
fn packed_records_match_mldsa65_and_reject_tampering() {
    exercise::<MlDsa65>();
}
