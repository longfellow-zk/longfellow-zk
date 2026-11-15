// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Complete hidden-key proofs; the verifier receives no encoded public key.
use longfellow_zk::{
    mldsa::{
        development_provider::compile_hidden_with_backend,
        proto::{BinaryKeccak, KeccakBackend, MlDsa44, MlDsa65, MlDsaParams},
        runtime::{hidden, reference::ConcreteInstance},
        testcases as vectors,
    },
    runtime::random::DeterministicRng,
};
fn exercise<P: MlDsaParams>(source: &str, marker: &str, backend: KeccakBackend) {
    let e = vectors::first_cpp_example(source, marker);
    let instance = ConcreteInstance::<P>::new(&e[1], &e[4], &e[0], &e[2]).unwrap();
    let keccak = BinaryKeccak {
        external_permutations: backend != KeccakBackend::Scalar,
        ..BinaryKeccak::default()
    };
    let c = compile_hidden_with_backend::<P>(keccak, backend).unwrap();
    let proof = hidden::prove(
        &c,
        &e[1],
        &instance,
        b"hidden test",
        &mut DeterministicRng::new(51),
    )
    .unwrap();
    hidden::verify::<P>(&c, b"hidden test", &proof).unwrap();
    assert!(hidden::verify::<P>(&c, b"wrong context", &proof).is_err());
    // The native sextic codec must reject each noncanonical prime coordinate,
    // even though the surrounding GF128 values accept every 16-byte string.
    let native_start = 8 + 32 + 2 * 16;
    for coordinate in 0..6 {
        let mut bad = proof.clone();
        let start = native_start + coordinate * 3;
        bad[start..start + 3].copy_from_slice(&8_380_417u32.to_le_bytes()[..3]);
        assert!(hidden::verify::<P>(&c, b"hidden test", &bad).is_err());
    }
    if P::K == MlDsa44::K {
        assert!(hidden::verify::<MlDsa65>(&c, b"hidden test", &proof).is_err());
    } else {
        assert!(hidden::verify::<MlDsa44>(&c, b"hidden test", &proof).is_err());
    }

    for n in [0, 8, proof.len() / 2, proof.len() - 1] {
        assert!(hidden::verify::<P>(&c, b"hidden test", &proof[..n]).is_err());
    }
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(hidden::verify::<P>(&c, b"hidden test", &trailing).is_err());
    for i in [0, 40, proof.len() / 2, proof.len() - 1] {
        let mut bad = proof.clone();
        bad[i] ^= 1;
        assert!(hidden::verify::<P>(&c, b"hidden test", &bad).is_err());
    }
    let mut wrong_key = e[1].clone();
    wrong_key[0] ^= 1;
    assert!(hidden::prove(
        &c,
        &wrong_key,
        &instance,
        b"hidden test",
        &mut DeterministicRng::new(52)
    )
    .is_err());
    let mut bad_instance = instance;
    bad_instance.signature.z_bits[0][0] ^= 1;
    assert!(hidden::prove(
        &c,
        &e[1],
        &bad_instance,
        b"hidden test",
        &mut DeterministicRng::new(53)
    )
    .is_err());
}
macro_rules! vector {
    ($name:literal) => {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../lib/circuits/tests/pq/ml_dsa/",
            $name
        ))
    };
}
#[test]
fn hidden_scalar_44() {
    exercise::<MlDsa44>(
        vector!("ml_dsa_44_examples.cc"),
        "GetMlDsa44Examples()",
        KeccakBackend::Scalar,
    )
}
#[test]
fn hidden_simd_44() {
    exercise::<MlDsa44>(
        vector!("ml_dsa_44_examples.cc"),
        "GetMlDsa44Examples()",
        KeccakBackend::Permutations,
    )
}
#[test]
fn hidden_scalar_65() {
    exercise::<MlDsa65>(
        vector!("ml_dsa_65_examples.cc"),
        "GetMlDsa65Examples()",
        KeccakBackend::Scalar,
    )
}
#[test]
fn hidden_simd_65() {
    exercise::<MlDsa65>(
        vector!("ml_dsa_65_examples.cc"),
        "GetMlDsa65Examples()",
        KeccakBackend::Permutations,
    )
}

#[test]
fn hidden_rounds_44() {
    exercise::<MlDsa44>(
        vector!("ml_dsa_44_examples.cc"),
        "GetMlDsa44Examples()",
        KeccakBackend::Rounds,
    )
}
#[test]
fn hidden_rounds_65() {
    exercise::<MlDsa65>(
        vector!("ml_dsa_65_examples.cc"),
        "GetMlDsa65Examples()",
        KeccakBackend::Rounds,
    )
}
