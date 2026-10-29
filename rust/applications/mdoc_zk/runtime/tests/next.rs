// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    compile::algebra::CompileNat,
    mdoc::{
        circuits::parse_test_data,
        development_provider,
        runtime::v2::{self, req_attr},
    },
    runtime::random::DeterministicRng,
};
#[test]
fn next_v9_two_and_four_attributes() {
    let data = &crate::mdoc::testcases::vectors::TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let attrs = parsed
        .attrs
        .iter()
        .cycle()
        .take(4)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    for n in [2, 4] {
        let b = development_provider::compile_next(n).unwrap();
        assert_eq!(b.spec().version, 9);
        let proof = v2::run_mdoc_prover_inner(
            b.spec(),
            b.compressed(),
            data.mdoc,
            data.pkx,
            data.pky,
            data.transcript,
            &attrs[..n],
            now,
            data.doc_type,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        v2::run_mdoc_verifier_inner(
            b.spec(),
            b.compressed(),
            data.pkx,
            data.pky,
            data.transcript,
            &attrs[..n],
            now,
            data.doc_type,
            &proof,
        )
        .unwrap();
        let mut bad = proof;
        let end = bad.len() - 1;
        bad[end] ^= 1;
        assert!(v2::run_mdoc_verifier_inner(
            b.spec(),
            b.compressed(),
            data.pkx,
            data.pky,
            data.transcript,
            &attrs[..n],
            now,
            data.doc_type,
            &bad
        )
        .is_err());
    }
}
#[test]
fn manifest_codec_and_boolean_witness_contract() {
    use crate::{
        mdoc::proto::packed::HashInputManifest as M, runtime::algebra::gf2_128::Gf2_128 as E,
    };
    let m = M {
        public_bits: 1,
        private_bits: 1,
    };
    let bytes = m.to_bytes();
    assert_eq!(M::from_bytes(&bytes).unwrap(), m);
    for n in 0..bytes.len() {
        assert!(M::from_bytes(&bytes[..n]).is_err());
    }
    assert!(m.validate_witness(&[E::from(0)], &[E::from(1)]).is_ok());
    assert!(m.validate_witness(&[E::from(2)], &[E::from(1)]).is_err());
    assert!(M {
        public_bits: usize::MAX,
        private_bits: 1
    }
    .validate()
    .is_err());
}
