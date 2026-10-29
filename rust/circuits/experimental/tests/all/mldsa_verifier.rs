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

use super::mldsa_test_vectors::first_cpp_example;
use crate::{
    circuits::experimental::mldsa::{
        params::{MlDsa44, MlDsa65, MlDsaParams},
        runtime::verifier::ConcreteInstance,
    },
    compile::{algebra::fp24_ext6::CompileFp24Ext6, eval::FieldID},
    core::algebra::AlgebraicField,
    runtime::algebra::fp24_ext6::RuntimeFp24Ext6,
};

#[path = "../support/mldsa.rs"]
mod support;

fn check<P: MlDsaParams>(example: &[Vec<u8>]) {
    let instance =
        ConcreteInstance::<P>::new(&example[1], &example[4], &example[0], &example[2]).unwrap();
    assert_eq!(instance.mu.as_slice(), example[3]);
    let cf = CompileFp24Ext6::new();
    let rf = RuntimeFp24Ext6::new();
    let (circuit, _, symbols) = support::compile_verifier::<P>(&cf);
    let segmented = crate::compile::compiler::segment_circuit_v2(&cf, &circuit);
    let mut inputs = crate::compile::eval::initial_inputs(&rf);
    instance.push_wires(&rf, &mut inputs);
    crate::compile::eval::eval_circuit_fc(&cf, &rf, &segmented, &symbols, &inputs, FieldID::None)
        .unwrap()
        .assert_all_passed();
    // mu is private, but bound to the challenge hash inside the circuit.
    let last = inputs.len() - 1;
    inputs[last] = rf.subf(&rf.one(), &inputs[last]);
    let result = crate::compile::eval::eval_circuit_fc(
        &cf,
        &rf,
        &segmented,
        &symbols,
        &inputs,
        FieldID::None,
    );
    assert!(result.is_err() || result.unwrap().result.is_err());
}

#[test]
fn full_mldsa44_accepts_cpp_vector_and_rejects_corruption() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc");
    check::<MlDsa44>(&first_cpp_example(source, "GetMlDsa44Examples()"));
}

#[test]
fn full_mldsa65_accepts_cpp_vector_and_rejects_corruption() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc");
    check::<MlDsa65>(&first_cpp_example(source, "GetMlDsa65Examples()"));
}
