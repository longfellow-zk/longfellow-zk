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

use circuits_bitvec::BitvecLogic;
use circuits_experimental::mldsa::{
    algebra::{CompileFp24Ext6, RuntimeFp24Ext6},
    shake::{allocate_witness, permutation_count, shake128, shake256_witness, Shake256},
};
use compile_eval::FieldID;
use compile_logic::Logic;
use core_algebra::{AlgebraicField, HasLookupPoints};

#[test]
fn native_shake256_matches_the_empty_string_vector() {
    let (output, witness) = shake256_witness(&[], 64);
    let expected = [
        0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb,
        0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5,
        0x76, 0x2f, 0xd7, 0x5d, 0xc4, 0xdd, 0xd8, 0xc0, 0xf2, 0x00, 0xcb, 0x05, 0x01, 0x9d, 0x67,
        0xb5, 0x92, 0xf6, 0xfc, 0x82, 0x1c, 0x49, 0x47, 0x9a, 0xb4, 0x86, 0x40, 0x29, 0x2e, 0xac,
        0xb3, 0xb7, 0xc4, 0xbe,
    ];
    assert_eq!(output, expected);
    assert_eq!(witness.permutations.len(), permutation_count(0, 64));
}

#[test]
fn native_shake_accepts_zero_output_bytes() {
    let (output, witness) = shake256_witness(b"abc", 0);
    assert!(output.is_empty());
    assert_eq!(witness.permutations.len(), permutation_count(3, 0));
    assert!(shake128(b"abc", 0).is_empty());
}

#[test]
fn shake256_handles_absorb_and_squeeze_boundaries() {
    for &(input_len, output_len) in &[(135, 137), (136, 272), (137, 273)] {
        let input: Vec<_> = (0..input_len).map(|i| i as u8).collect();
        let (output, witness) = shake256_witness(&input, output_len);
        assert_eq!(output.len(), output_len);
        assert_eq!(
            witness.permutations.len(),
            permutation_count(input_len, output_len)
        );
    }
}

#[test]
fn compiled_shake256_accepts_the_native_witness() {
    let expected = shake256_witness(&[], 32).0;
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
        let bitvec = BitvecLogic::new(&logic);
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let witness = allocate_witness(&bitvec, &mut position, 0, expected.len());
        let shake = Shake256::new(&logic);
        let (output, permutation_assertions) = shake.assert_hash(&[], expected.len(), &witness);
        let output_assertions = logic.assert_mapi("output", 0..expected.len(), |i| {
            bitvec.assert_eq("byte", &output[i], &bitvec.of_u64(expected[i] as u64))
        });
        (
            logic.assert_all(
                "compiled_shake256",
                &[permutation_assertions, output_assertions],
            ),
            1,
            0,
        )
    });

    let (_, concrete_witness) = shake256_witness(&[], expected.len());
    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    concrete_witness.push_wires(&runtime_field, &mut inputs);
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

    // Flip a represented bit while keeping the encoded input a valid point.
    // This must fail the transition check, not just the decoder's range check.
    let first = compile_logic::K_FIRST_WIRE_POSITION;
    let bits = circuits_experimental::mldsa::shake::plucker_bits();
    if bits == 0 {
        inputs[first] = runtime_field.neg(&inputs[first]);
    } else {
        let value = (concrete_witness.permutations[0].intermediate_states[0][0][0]
            & ((1u64 << bits) - 1)) as usize;
        inputs[first] = runtime_field.lookup_point((1 << bits) + 1, value ^ 1);
    }
    let corrupted = compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &circuit,
        &symbols,
        &inputs,
        FieldID::None,
    )
    .unwrap();
    assert!(
        corrupted.is_err(),
        "accepted a different valid represented SHAKE state bit"
    );
    if bits > 0 {
        inputs[first] = runtime_field.lookup_point((1 << bits) + 1, 1 << bits);
        let outside = compile_eval::eval_circuit_fc(
            &compile_field,
            &runtime_field,
            &circuit,
            &symbols,
            &inputs,
            FieldID::None,
        )
        .unwrap();
        assert!(
            outside.is_err(),
            "accepted the excluded plucker lookup point"
        );
    }
}
