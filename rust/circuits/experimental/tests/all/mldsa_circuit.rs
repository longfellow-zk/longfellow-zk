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

use circuits_boolean::BooleanIO;
use circuits_experimental::mldsa::{
    algebra::{CompileFp24Ext6, RuntimeFp24Ext6},
    circuit::{MlDsaCircuit, PolynomialW},
    params::{MlDsa44, MlDsa65, MlDsaParams, N},
    reference::{decompose, ntt, use_hint, Polynomial},
};
use compile_eval::FieldID;
use compile_logic::LogicIO;

#[test]
fn compiled_ntt_accepts_the_native_transform() {
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let input = PolynomialW::input(&logic, &mut position);
        let expected = PolynomialW::input(&logic, &mut position);
        let mldsa = MlDsaCircuit::<_, MlDsa44>::new(&logic);
        (mldsa.assert_ntt(&input, &expected), 1, 0)
    });

    let input: Polynomial = std::array::from_fn(|i| (17 * i as u32 + 9) % 8_380_417);
    let mut expected = input;
    ntt(&mut expected);
    let mut values = compile_eval::initial_inputs(&runtime_field);
    values.extend(
        input
            .iter()
            .chain(&expected)
            .map(|&value| runtime_field.from_coefficients([value, 0, 0, 0, 0, 0])),
    );

    compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &circuit,
        &symbols,
        &values,
        FieldID::None,
    )
    .unwrap()
    .assert_all_passed();
}

#[test]
fn compiled_use_hint_accepts_both_sign_branches() {
    for value in [123_456i32, 8_200_000i32] {
        let (raw_high, raw_low) = decompose::<MlDsa44>(value);
        let hinted_high = use_hint::<MlDsa44>(true, value);
        let shifted = (raw_low + 95_232) as u64;
        let aux = shifted | (u64::from(raw_low <= 0) << 18);
        let compile_field = CompileFp24Ext6::new();
        let runtime_field = RuntimeFp24Ext6::new();
        let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
            let mut position = compile_logic::K_FIRST_WIRE_POSITION;
            let hint = logic.next(&mut position);
            let value_wire = logic.next(&mut position);
            let raw = logic.next(&mut position);
            let boolean_io = BooleanIO::new(&logic);
            let raw_bits: Vec<_> = (0..6).map(|_| boolean_io.next(&mut position)).collect();
            let aux_bits: Vec<_> = (0..19).map(|_| boolean_io.next(&mut position)).collect();
            let hinted = logic.next(&mut position);
            let hinted_bits: Vec<_> = (0..6).map(|_| boolean_io.next(&mut position)).collect();
            let mldsa = MlDsaCircuit::<_, MlDsa44>::new(&logic);
            (
                mldsa.assert_use_hint_single(
                    &hint,
                    &value_wire,
                    &raw,
                    &raw_bits,
                    &aux_bits,
                    &hinted,
                    &hinted_bits,
                ),
                1,
                0,
            )
        });

        let mut inputs = compile_eval::initial_inputs(&runtime_field);
        inputs.push(runtime_field.from_coefficients([1, 0, 0, 0, 0, 0]));
        inputs.push(runtime_field.from_coefficients([value as u32, 0, 0, 0, 0, 0]));
        inputs.push(runtime_field.from_coefficients([raw_high as u32, 0, 0, 0, 0, 0]));
        circuits_bitvec::concrete::push_bitvec_u64(&runtime_field, raw_high as u64, 6, &mut inputs);
        circuits_bitvec::concrete::push_bitvec_u64(&runtime_field, aux, 19, &mut inputs);
        inputs.push(runtime_field.from_coefficients([hinted_high, 0, 0, 0, 0, 0]));
        circuits_bitvec::concrete::push_bitvec_u64(
            &runtime_field,
            u64::from(hinted_high),
            6,
            &mut inputs,
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
}

fn check_invalid_norm_rejected<P: MlDsaParams>() {
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let polynomial = PolynomialW::input(&logic, &mut position);
        let boolean_io = BooleanIO::new(&logic);
        let bits = vec![(0..N)
            .map(|_| {
                (0..P::Z_BITS)
                    .map(|_| boolean_io.next(&mut position))
                    .collect()
            })
            .collect()];
        let mldsa = MlDsaCircuit::<_, P>::new(&logic);
        (
            mldsa.assert_infinity_norm(
                "invalid_norm",
                &[polynomial],
                &bits,
                P::Z_BITS,
                P::GAMMA1 - P::REJECTION_BOUND,
            ),
            1,
            0,
        )
    });

    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    for coefficient in 0..N {
        let value = if coefficient == 0 { bound } else { 0 };
        inputs.push(runtime_field.from_coefficients([value, 0, 0, 0, 0, 0]));
    }
    for coefficient in 0..N {
        let shifted = if coefficient == 0 {
            2 * bound - 1
        } else {
            bound - 1
        };
        circuits_bitvec::concrete::push_bitvec_u64(
            &runtime_field,
            u64::from(shifted),
            P::Z_BITS,
            &mut inputs,
        );
    }
    let result = compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &circuit,
        &symbols,
        &inputs,
        FieldID::None,
    )
    .unwrap();
    assert!(result.is_err(), "accepted a coefficient at the norm bound");
}

#[test]
fn compiled_infinity_norm_rejects_boundary_for_both_parameter_sets() {
    check_invalid_norm_rejected::<MlDsa44>();
    check_invalid_norm_rejected::<MlDsa65>();
}

fn check_invalid_hint_sign_rejected<P: MlDsaParams>() {
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, _stats, symbols) = compile_compiler::compile(&compile_field, |logic| {
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let hint = logic.next(&mut position);
        let value = logic.next(&mut position);
        let raw = logic.next(&mut position);
        let boolean_io = BooleanIO::new(&logic);
        let raw_bits: Vec<_> = (0..P::R1_BITS)
            .map(|_| boolean_io.next(&mut position))
            .collect();
        let auxiliary_bits: Vec<_> = (0..P::r0_bits() + 1)
            .map(|_| boolean_io.next(&mut position))
            .collect();
        let hinted = logic.next(&mut position);
        let hinted_bits: Vec<_> = (0..P::R1_BITS)
            .map(|_| boolean_io.next(&mut position))
            .collect();
        let mldsa = MlDsaCircuit::<_, P>::new(&logic);
        (
            mldsa.assert_use_hint_single(
                &hint,
                &value,
                &raw,
                &raw_bits,
                &auxiliary_bits,
                &hinted,
                &hinted_bits,
            ),
            1,
            0,
        )
    });

    let raw_high = 5;
    let low = 1;
    let value = (raw_high * 2 * P::GAMMA2 + low) % 8_380_417;
    let shifted_low = P::GAMMA2 + low;
    let invalid_sign = 1u64;
    let auxiliary = u64::from(shifted_low) | (invalid_sign << P::r0_bits());
    let invalid_hinted_high = raw_high - 1;
    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    inputs.push(runtime_field.from_coefficients([1, 0, 0, 0, 0, 0]));
    inputs.push(runtime_field.from_coefficients([value, 0, 0, 0, 0, 0]));
    inputs.push(runtime_field.from_coefficients([raw_high, 0, 0, 0, 0, 0]));
    circuits_bitvec::concrete::push_bitvec_u64(
        &runtime_field,
        u64::from(raw_high),
        P::R1_BITS,
        &mut inputs,
    );
    circuits_bitvec::concrete::push_bitvec_u64(
        &runtime_field,
        auxiliary,
        P::r0_bits() + 1,
        &mut inputs,
    );
    inputs.push(runtime_field.from_coefficients([invalid_hinted_high, 0, 0, 0, 0, 0]));
    circuits_bitvec::concrete::push_bitvec_u64(
        &runtime_field,
        u64::from(invalid_hinted_high),
        P::R1_BITS,
        &mut inputs,
    );
    let result = compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &circuit,
        &symbols,
        &inputs,
        FieldID::None,
    )
    .unwrap();
    assert!(result.is_err(), "accepted an invalid UseHint sign witness");
}

#[test]
fn compiled_use_hint_rejects_invalid_sign_for_both_parameter_sets() {
    check_invalid_hint_sign_rejected::<MlDsa44>();
    check_invalid_hint_sign_rejected::<MlDsa65>();
}
