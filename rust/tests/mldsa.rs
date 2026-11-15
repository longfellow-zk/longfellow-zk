// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public-key two-field proofs and rejection at the application boundary.
use longfellow_zk::{
    mldsa::{
        development_provider::prepare_public_with_backend,
        proto::{BinaryKeccak, KeccakBackend, MlDsa44, MlDsa65, MlDsaParams},
        runtime::{
            self,
            reference::{self as algorithm, ConcreteInstance},
        },
        testcases as vectors,
    },
    runtime::random::DeterministicRng,
};
fn exercise<P: MlDsaParams>(source: &str, marker: &str, backend: KeccakBackend) {
    let e = vectors::first_cpp_example(source, marker);
    assert!(algorithm::verify::<P>(&e[1], &e[4], &e[0], &e[2]));
    let instance = ConcreteInstance::<P>::new(&e[1], &e[4], &e[0], &e[2]).unwrap();
    assert_eq!(instance.mu.as_slice(), e[3]);
    let keccak = BinaryKeccak {
        external_permutations: backend != KeccakBackend::Scalar,
        ..BinaryKeccak::default()
    };
    let circuits = prepare_public_with_backend::<P>(keccak, backend).load();
    let proof = runtime::prove(
        &circuits,
        &e[1],
        &instance,
        b"test",
        &mut DeterministicRng::new(71),
    )
    .unwrap();
    runtime::verify::<P>(&circuits, &e[1], b"test", &proof).unwrap();
    assert!(runtime::verify::<P>(&circuits, &e[1], b"other", &proof).is_err());
    let mut wrong_key = e[1].clone();
    wrong_key[0] ^= 1;
    assert!(runtime::verify::<P>(&circuits, &wrong_key, b"test", &proof).is_err());
    assert!(runtime::verify::<P>(&circuits, &e[1][1..], b"test", &proof).is_err());
    for n in [0, 8, proof.len() / 2, proof.len() - 1] {
        assert!(runtime::verify::<P>(&circuits, &e[1], b"test", &proof[..n]).is_err());
    }
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(runtime::verify::<P>(&circuits, &e[1], b"test", &trailing).is_err());
    for i in [0, 8, 40, 104, proof.len() - 1] {
        let mut corrupted = proof.clone();
        corrupted[i] ^= 1;
        assert!(runtime::verify::<P>(&circuits, &e[1], b"test", &corrupted).is_err());
    }
    // Each mutation reaches a different circuit predicate or the cross-field
    // relation, rather than merely failing the native signature decoder.
    for which in 0..3 {
        let mut bad = instance.clone();
        match which {
            0 => bad.signature.z_bits[0][0] ^= 1,
            1 => bad.signature.h[0][0] ^= 1,
            _ => bad.mu[0] ^= 1,
        }
        assert!(runtime::prove(
            &circuits,
            &e[1],
            &bad,
            b"test",
            &mut DeterministicRng::new(91)
        )
        .is_err());
    }
}

#[test]
fn public_key_mldsa44() {
    exercise::<MlDsa44>(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"
        )),
        "GetMlDsa44Examples()",
        KeccakBackend::Scalar,
    );
}

#[test]
fn public_key_mldsa65() {
    exercise::<MlDsa65>(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"
        )),
        "GetMlDsa65Examples()",
        KeccakBackend::Scalar,
    );
}

macro_rules! packed_test {
    ($name:ident, $params:ty, $fixture:literal, $marker:literal, $backend:ident) => {
        #[test]
        fn $name() {
            exercise::<$params>(
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../lib/circuits/tests/pq/ml_dsa/",
                    $fixture
                )),
                $marker,
                KeccakBackend::$backend,
            );
        }
    };
}
packed_test!(
    public_permutations_44,
    MlDsa44,
    "ml_dsa_44_examples.cc",
    "GetMlDsa44Examples()",
    Permutations
);
packed_test!(
    public_rounds_44,
    MlDsa44,
    "ml_dsa_44_examples.cc",
    "GetMlDsa44Examples()",
    Rounds
);
packed_test!(
    public_permutations_65,
    MlDsa65,
    "ml_dsa_65_examples.cc",
    "GetMlDsa65Examples()",
    Permutations
);
packed_test!(
    public_rounds_65,
    MlDsa65,
    "ml_dsa_65_examples.cc",
    "GetMlDsa65Examples()",
    Rounds
);

#[test]
fn shake_matches_independent_xof_at_padding_and_squeeze_boundaries() {
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    for len in [0, 1, 135, 136, 137, 167, 168, 271, 272] {
        let input: Vec<_> = (0..len).map(|i| i as u8).collect();
        let mut s256 = sha3::Shake256::default();
        s256.update(&input);
        let mut expected = vec![0; 300];
        s256.finalize_xof().read(&mut expected);
        assert_eq!(algorithm::shake256_witness(&input, 300).0, expected);
        let mut s128 = sha3::Shake128::default();
        s128.update(&input);
        s128.finalize_xof().read(&mut expected);
        assert_eq!(algorithm::shake128(&input, 300), expected);
    }
}
