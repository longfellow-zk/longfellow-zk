// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    run_mdoc_prover_inner, run_mdoc_prover_inner_with_encoding, run_mdoc_verifier,
    run_mdoc_verifier_with_encoding, SignatureEncoding,
};
use crate::{
    mdoc::{
        cbor::test_utils::parse_test_data,
        development_provider::compile_parser_free_next,
        testcases::TEST_DATA,
        v2::{self, decompress_circuits, req_attr},
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, RuntimeNat},
        random::DeterministicRng,
    },
};

#[test]
fn canonical_single_commitment_roundtrip_and_statement_binding() {
    let provided = compile_parser_free_next(2).unwrap();
    let (_, hash) = decompress_circuits(
        provided.compressed(),
        &P256Field::new(),
        &Gf2_128Field::new(),
    )
    .unwrap();
    // The native-arity v2 compiler's parser-free two-attribute circuit ID.
    assert_eq!(
        hash.id,
        [
            51, 204, 152, 190, 65, 178, 159, 41, 193, 12, 189, 224, 177, 128, 180, 214, 192, 34,
            219, 11, 122, 239, 15, 45, 216, 126, 202, 120, 10, 192, 37, 84
        ]
    );
    let data = &TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, RuntimeNat<4>>(data);
    let attrs = parsed
        .attrs
        .iter()
        .take(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    let proof = run_mdoc_prover_inner_with_encoding(
        provided.spec(),
        provided.compressed(),
        data.mdoc,
        data.pkx,
        data.pky,
        data.transcript,
        &attrs,
        now,
        data.doc_type,
        SignatureEncoding::Canonical,
        &mut DeterministicRng::new(57),
    )
    .unwrap();
    let verify = |statement: &[u8], request: &[_], bytes: &[u8]| {
        run_mdoc_verifier_with_encoding(
            provided.spec(),
            provided.compressed(),
            data.pkx,
            data.pky,
            statement,
            request,
            now,
            data.doc_type,
            bytes,
            SignatureEncoding::Canonical,
        )
    };
    verify(data.transcript, &attrs, &proof).unwrap();
    let mut changed_statement = data.transcript.to_vec();
    changed_statement.push(0);
    assert!(verify(&changed_statement, &attrs, &proof).is_err());
    let mut changed_attrs = attrs.clone();
    changed_attrs[0].id.push(b'x');
    assert!(verify(data.transcript, &changed_attrs, &proof).is_err());
    let mut corrupted = proof.clone();
    *corrupted.last_mut().unwrap() ^= 1;
    assert!(verify(data.transcript, &attrs, &corrupted).is_err());
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(verify(data.transcript, &attrs, &trailing).is_err());
    assert!(v2::run_mdoc_verifier(
        provided.spec(),
        provided.compressed(),
        data.pkx,
        data.pky,
        data.transcript,
        &attrs,
        now,
        data.doc_type,
        &proof
    )
    .is_err());
}

#[test]
fn affine_ers_roundtrip_preserves_circuits_and_binds_encoding() {
    use super::{proof_geometry, proof_geometry_with_encoding};
    assert_eq!(SignatureEncoding::default(), SignatureEncoding::AffineErs);
    let provided = compile_parser_free_next(2).unwrap();
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let (signature, hash) = decompress_circuits(provided.compressed(), &p, &f).unwrap();
    // Current parser-free v2 signature circuit, shared by both encodings.
    assert_eq!(
        signature.id,
        [
            146, 236, 152, 155, 23, 54, 49, 225, 99, 68, 102, 201, 228, 213, 78, 231, 196, 51, 225,
            85, 151, 134, 183, 121, 10, 161, 193, 141, 21, 224, 2, 147
        ]
    );
    let canonical = proof_geometry_with_encoding(
        provided.spec(),
        &signature,
        &hash,
        SignatureEncoding::Canonical,
    )
    .unwrap();
    let affine = proof_geometry_with_encoding(
        provided.spec(),
        &signature,
        &hash,
        SignatureEncoding::AffineErs,
    )
    .unwrap();
    // Pin both composed schedules after upper less-than flattening.
    assert_eq!(
        canonical.binary().sumcheck().layers(),
        &[2, 6, 7, 7, 9, 9, 9, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 20, 21, 21]
    );
    assert_eq!(
        affine.binary().sumcheck().layers(),
        &[6, 7, 7, 8, 9, 9, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 20, 21, 21]
    );
    assert_eq!(canonical.signature(), affine.signature());
    assert_eq!(
        canonical.signature().layers(),
        &[4, 5, 6, 11, 11, 13, 14, 14, 14, 14, 12]
    );
    assert!(
        affine.binary().sumcheck().layers().iter().sum::<usize>()
            < canonical.binary().sumcheck().layers().iter().sum::<usize>()
    );
    assert_eq!(canonical.binary().sumcheck().layers().last(), Some(&21));
    assert_eq!(affine.binary().sumcheck().layers().last(), Some(&21));
    let default = proof_geometry(provided.spec(), &signature, &hash).unwrap();
    assert_eq!(
        default.binary().sumcheck().layers(),
        affine.binary().sumcheck().layers()
    );
    let data = &TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, RuntimeNat<4>>(data);
    let attrs = parsed
        .attrs
        .iter()
        .take(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    let proof = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        data.mdoc,
        data.pkx,
        data.pky,
        data.transcript,
        &attrs,
        now,
        data.doc_type,
        &mut DeterministicRng::new(57),
    )
    .unwrap();
    let verify = |bytes: &[u8], encoding| {
        run_mdoc_verifier_with_encoding(
            provided.spec(),
            provided.compressed(),
            data.pkx,
            data.pky,
            data.transcript,
            &attrs,
            now,
            data.doc_type,
            bytes,
            encoding,
        )
    };
    run_mdoc_verifier(
        provided.spec(),
        provided.compressed(),
        data.pkx,
        data.pky,
        data.transcript,
        &attrs,
        now,
        data.doc_type,
        &proof,
    )
    .unwrap();
    verify(&proof, SignatureEncoding::AffineErs).unwrap();
    assert!(verify(&proof, SignatureEncoding::Canonical).is_err());
    let mut tampered = proof.clone();
    *tampered.last_mut().unwrap() ^= 1;
    assert!(verify(&tampered, SignatureEncoding::AffineErs).is_err());
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(verify(&trailing, SignatureEncoding::AffineErs).is_err());
    // Current parser-free hash circuit; encoding does not alter it.
    assert_eq!(
        hash.id,
        [
            51, 204, 152, 190, 65, 178, 159, 41, 193, 12, 189, 224, 177, 128, 180, 214, 192, 34,
            219, 11, 122, 239, 15, 45, 216, 126, 202, 120, 10, 192, 37, 84
        ]
    );
}
