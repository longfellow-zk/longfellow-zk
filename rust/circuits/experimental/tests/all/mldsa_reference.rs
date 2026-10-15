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

use circuits_experimental::mldsa::{
    algebra::Q,
    params::{MlDsa44, MlDsa65, MlDsaParams, N},
    reference::{inverse_ntt, ntt, ring_mul, simple_bit_pack, simple_bit_unpack, use_hint, verify},
};

#[test]
fn parameter_sets_match_fips_sizes() {
    assert_eq!(MlDsa44::public_key_bytes(), 1_312);
    assert_eq!(MlDsa44::signature_bytes(), 2_420);
    assert_eq!(MlDsa44::use_hint_modulus(), 44);
    assert_eq!(MlDsa65::public_key_bytes(), 1_952);
    assert_eq!(MlDsa65::signature_bytes(), 3_309);
    assert_eq!(MlDsa65::use_hint_modulus(), 16);
}

#[test]
fn native_verifier_accepts_cpp_44_and_65_examples() {
    let source44 =
        include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc");
    let example44 = first_cpp_example(source44, "GetMlDsa44Examples()");
    assert_eq!(example44[3].len(), 64);
    assert!(verify::<MlDsa44>(
        &example44[1],
        &example44[4],
        &example44[0],
        &example44[2]
    ));

    let source65 =
        include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc");
    let example65 = first_cpp_example(source65, "GetMlDsa65Examples()");
    assert_eq!(example65[3].len(), 64);
    assert!(verify::<MlDsa65>(
        &example65[1],
        &example65[4],
        &example65[0],
        &example65[2]
    ));
}

#[test]
fn native_verifier_rejects_malformed_encodings() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc");
    let example = first_cpp_example(source, "GetMlDsa44Examples()");

    let mut changed_signature = example[4].clone();
    changed_signature[0] ^= 1;
    assert!(!verify::<MlDsa44>(
        &example[1],
        &changed_signature,
        &example[0],
        &example[2]
    ));

    let mut extended_signature = example[4].clone();
    extended_signature.push(0);
    assert!(!verify::<MlDsa44>(
        &example[1],
        &extended_signature,
        &example[0],
        &example[2]
    ));

    let mut extended_public_key = example[1].clone();
    extended_public_key.push(0);
    assert!(!verify::<MlDsa44>(
        &extended_public_key,
        &example[4],
        &example[0],
        &example[2]
    ));
}

#[test]
fn ntt_round_trip_and_negacyclic_product() {
    let polynomial = std::array::from_fn(|i| ((i * i + 17 * i + 3) as u32) % Q);
    let mut transformed = polynomial;
    ntt(&mut transformed);
    inverse_ntt(&mut transformed);
    assert_eq!(transformed, polynomial);

    let mut x = [0u32; N];
    x[1] = 1;
    let mut x_to_255 = [0u32; N];
    x_to_255[N - 1] = 1;
    let product = ring_mul(&x, &x_to_255);
    assert_eq!(product[0], Q - 1);
    assert!(product[1..].iter().all(|&coefficient| coefficient == 0));
}

#[test]
fn packing_and_hint_primitives_cover_both_parameter_sets() {
    let coefficients = std::array::from_fn(|i| (i % 1024) as u32);
    let packed = simple_bit_pack(&coefficients, 1023).unwrap();
    assert_eq!(simple_bit_unpack(&packed, 1023).unwrap(), coefficients);

    assert_eq!(use_hint::<MlDsa44>(false, 0), 0);
    assert_eq!(use_hint::<MlDsa44>(true, 1), 1);
    assert_eq!(use_hint::<MlDsa44>(true, -1), 43);
    assert_eq!(use_hint::<MlDsa65>(true, -1), 15);
}
