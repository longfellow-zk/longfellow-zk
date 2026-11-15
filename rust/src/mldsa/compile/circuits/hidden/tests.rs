// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Native coefficients are checked against an independent ML-DSA witness.
use super::*;
use crate::{
    compile::{
        algebra::fp24_ext6::CompileFp24Ext6,
        compiler::{compile_v2, segment_circuit_v2},
    },
    core::{
        algebra::{fp24::Q, AlgebraicField, SupportsU64Conversions},
        proto::v2::{CircuitReader, CircuitWriter},
    },
    mldsa::{
        compile::native_inputs,
        proto::{shared_widths, MlDsa44, MlDsa65, MlDsaParams, N},
        runtime::reference::{decode_public_key, ConcreteInstance},
        testcases as vectors,
    },
    runtime::{algebra::fp24_ext6::RuntimeFp24Ext6, v2::sumcheck::eval_circuit},
};
fn check<P: MlDsaParams>(text: &str, marker: &str) {
    let e = vectors::first_cpp_example(text, marker);
    let instance = ConcreteInstance::<P>::new(&e[1], &e[4], &e[0], &e[2]).unwrap();
    let key = decode_public_key::<P>(&e[1]).unwrap();
    let mut input_words: Vec<u64> = instance
        .signature
        .z_bits
        .iter()
        .flatten()
        .copied()
        .collect();
    input_words.extend(instance.witness.raw_high_bits.iter().flatten().copied());
    input_words.extend(
        instance
            .witness
            .hint_auxiliary_bits
            .iter()
            .flatten()
            .map(|v| v & ((1 << P::r0_bits()) - 1)),
    );
    input_words.extend(instance.witness.c.iter().map(|&v| u64::from(v == 1)));
    input_words.extend(instance.witness.c.iter().map(|&v| u64::from(v == Q - 1)));
    input_words.extend(key.a_hat.iter().flatten().flatten().map(|&v| u64::from(v)));
    input_words.extend(key.t1.iter().flatten().map(|&v| u64::from(v)));
    assert_eq!(input_words.len(), shared_widths::<P>().len());
    for (&value, width) in input_words.iter().zip(shared_widths::<P>()) {
        assert!(value < 1 << width);
    }
    input_words.extend(
        instance
            .witness
            .approximation
            .iter()
            .chain(&instance.witness.ntt_z)
            .chain([&instance.witness.ntt_c])
            .flatten()
            .map(|&v| u64::from(v)),
    );
    let compiler_field = CompileFp24Ext6::new();
    let (unsegmented, _, _) = compile_v2(&compiler_field, |logic| arithmetic::build::<P>(logic, 4));
    let compiled = segment_circuit_v2(&compiler_field, unsegmented);
    let bytes = CircuitWriter::new(&compiler_field).to_bytes(&compiled);
    let f = RuntimeFp24Ext6::new();
    let (c, tail) = CircuitReader::new(&f).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    assert_eq!(c.raw.ninput, native_inputs::<P>());
    let input: Vec<_> = input_words
        .into_iter()
        .map(|v| f.u64_to_element(v))
        .collect();
    eval_circuit(input.clone(), &c, &f).unwrap();
    let mut offset = 0;
    for count in [
        P::L * N,
        P::K * N,
        P::K * N,
        N,
        N,
        P::K * P::L * N,
        P::K * N,
        P::K * N,
        P::L * N,
        N,
    ] {
        for i in [offset, offset + count - 1] {
            let mut bad = input.clone();
            f.add(&mut bad[i], &f.one());
            assert!(
                eval_circuit(bad, &c, &f).is_err(),
                "unchecked native input {i}"
            );
        }
        offset += count;
    }
    assert_eq!(offset, input.len());
}
#[test]
fn compact_native_words_match_mldsa44_and_reject_each_changed_group() {
    check::<MlDsa44>(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"
        )),
        "GetMlDsa44Examples()",
    );
}
#[test]
fn compact_native_words_match_mldsa65_and_reject_each_changed_group() {
    check::<MlDsa65>(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"
        )),
        "GetMlDsa65Examples()",
    );
}
