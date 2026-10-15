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

use circuits_bitvec::{BitvecIO, BitvecLogic};
use circuits_experimental::mldsa::{
    algebra::{CompileFp24Ext6, RuntimeFp24Ext6, Q},
    circuit::PolynomialW,
    params::{MlDsa44, MlDsa65, MlDsaParams},
    sample::{allocate_witness, assert_sample_in_ball, sample_in_ball},
};
use compile_eval::FieldID;

fn check_sample<P: MlDsaParams>() {
    let seed: Vec<_> = (0..P::C_TILDE_BYTES).map(|i| (3 * i + 1) as u8).collect();
    let (challenge, witness) = sample_in_ball::<P>(&seed).unwrap();
    assert_eq!(witness.samples.len(), P::TAU);
    assert_eq!(
        challenge.iter().filter(|&&value| value != 0).count(),
        P::TAU
    );
    assert!(challenge
        .iter()
        .all(|&value| value == 0 || value == 1 || value == Q - 1));
}

#[test]
fn native_sample_in_ball_supports_44_and_65() {
    check_sample::<MlDsa44>();
    check_sample::<MlDsa65>();
}

#[test]
fn compiled_sample_in_ball_accepts_native_witness() {
    let seed: Vec<_> = (0..MlDsa44::C_TILDE_BYTES)
        .map(|i| (3 * i + 1) as u8)
        .collect();
    let (challenge, concrete_witness) = sample_in_ball::<MlDsa44>(&seed).unwrap();
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
        let bitvec = BitvecLogic::new(&logic);
        let bitvec_io = BitvecIO::new(&bitvec);
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let seed_wires: Vec<_> = (0..MlDsa44::C_TILDE_BYTES)
            .map(|_| bitvec_io.next(&mut position))
            .collect();
        let witness = allocate_witness::<_, MlDsa44>(&bitvec, &mut position);
        let challenge_wires = PolynomialW::input(&logic, &mut position);
        (
            assert_sample_in_ball::<_, MlDsa44>(&logic, &seed_wires, &challenge_wires, &witness),
            1,
            0,
        )
    });

    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    for &byte in &seed {
        circuits_bitvec::concrete::push_bitvec_u64(&runtime_field, u64::from(byte), 8, &mut inputs);
    }
    concrete_witness.push_wires(&runtime_field, &mut inputs);
    inputs.extend(
        challenge
            .iter()
            .map(|&value| runtime_field.from_coefficients([value, 0, 0, 0, 0, 0])),
    );
    compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &circuit,
        &symbols,
        &inputs,
        FieldID::None,
    )
    .unwrap()
    .assert_all_passed();
}
