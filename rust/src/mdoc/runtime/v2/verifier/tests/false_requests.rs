// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! False mdoc requests against the real NEXT circuits (the re-audit's probe
//! P4).
//!
//! A cheating prover holds a valid document and its honest witness for the
//! true request, but opens its transcript on a false request that differs in
//! one part: time outside the validity window, attribute value, attribute
//! identifier, document type, namespace, session transcript or issuer key.
//! Its self-checks are off (`transcript::cheat`). The verifier, given the
//! same false request, must reject every such proof; the true request must
//! verify.
use super::Fixture;
use crate::{
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        cbor::{parse::CborParser, test_utils::parse_test_data},
        testcases::TEST_DATA,
        v2::{
            circuits::Instance,
            document,
            inputs::{push_witness_hash, push_witness_sig, PublicInputs},
            link, req_attr,
            request::Request,
            run_mdoc_verifier, transcript, MdocProof, RequestedAttribute, ZkSpecStruct,
        },
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            q256::Q256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            secp256r1::Secp256r1,
            SupportsFFT,
        },
        random::DeterministicRng,
        v2::transcript::{cheat::cheating, Opened},
    },
};

/// A request: issuer key x and y, session transcript, attributes, time and
/// document type.
type Req<'a> = (
    &'a str,
    &'a str,
    &'a [u8],
    &'a [RequestedAttribute],
    &'a str,
    &'a str,
);

/// The request with issuer key `key`, the test session transcript, `attrs`,
/// `now` and document type `dt`.
fn req<'a>(
    key: (&'a str, &'a str),
    attrs: &'a [RequestedAttribute],
    now: &'a str,
    dt: &'a str,
) -> Req<'a> {
    (key.0, key.1, TEST_DATA.transcript, attrs, now, dt)
}

/// The checked request `r`.
fn check<'a>(spec: &'a ZkSpecStruct, r: Req<'a>, p256: &P256Field) -> Result<Request<'a>, String> {
    let (pkx, pky, tr, attrs, now, dt) = r;
    Request::check(spec, pkx, pky, tr, attrs, now, dt, p256).map_err(|e| format!("{e:?}"))
}

/// A cheating mdoc prover: the witness of the true request `honest`, the
/// statement (public inputs, session transcript) of the request `claimed`,
/// and the composition prover with its self-checks off.
fn prove_claimed(
    spec: &ZkSpecStruct,
    circuits: &[u8],
    honest: Req<'_>,
    claimed: Req<'_>,
    seed: u64,
) -> Result<Vec<u8>, String> {
    let p256 = P256Field::new();
    let (request0, request1) = (check(spec, honest, &p256)?, check(spec, claimed, &p256)?);
    let p256_2 = Fp2Field::new(&p256);
    let sig_domain = QuadraticExtensionFftInterpolatorFactory::new(
        &p256,
        &p256_2,
        p256_2.omega(),
        p256_2.omega_order(),
    );
    let gf2 = Gf2_128Field::new();
    let hash_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let instance = Instance::load(&request1, circuits, &p256, &gf2)?;
    let parsed = document::parse(TEST_DATA.mdoc, &request0, &p256)
        .map_err(|_| "honest document parse".to_string())?;
    let composition = link::composition(
        request1.spec(),
        instance.signature(),
        instance.hash(),
        (&hash_domain, &sig_domain),
    )?;
    let witness_hash =
        push_witness_hash(&request0, &parsed).map_err(|e| format!("hash witness: {e:?}"))?;
    let (q256, secp256r1) = (Q256Field::new(), Secp256r1::new(&p256));
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &request0, &parsed)
        .map_err(|_| "signature witness".to_string())?;
    let public = PublicInputs::derive(&request1, &p256);
    let statement = transcript::statement(&composition, &request1, &public)?;
    let mut rng = DeterministicRng::new(seed);
    let (body, tp) = cheating(|| {
        link::Statement::prove(Opened::new(&statement), witness_hash, witness_sig, &mut rng)
    })?;
    Ok(MdocProof { body }
        .write(statement.geometry(), &gf2, &p256, tp)?
        .into_bytes())
}

/// Every false request of one and of two attributes, each one part away from
/// the true request, is rejected even from a prover that ignores its own
/// checks; the true request verifies.
#[test]
fn cheating_provers_of_false_mdoc_requests_are_rejected() {
    let (issuer_pk, parsed, _) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let doc_type = "org.iso.18013.5.1.mDL";
    let ns = "org.iso.18013.5.1";
    let mut accepted = Vec::new();
    let mut unproved = Vec::new();
    for nattrs in [1usize, 2] {
        let fixture = Fixture::new(nattrs);
        let (pkx, pky, now) = (fixture.pkx.as_str(), fixture.pky.as_str(), fixture.now);
        let honest_attrs = &fixture.attrs[..];
        let honest: Req<'_> = (pkx, pky, TEST_DATA.transcript, honest_attrs, now, doc_type);
        let mut seed = 1u64;
        let mut run = |name: &str, claimed: Req<'_>, true_request: bool| {
            seed += 1;
            let spec = fixture.provided.spec();
            let circuits = fixture.provided.compressed();
            let proof = match prove_claimed(spec, circuits, honest, claimed, seed) {
                Ok(proof) => proof,
                Err(e) => return unproved.push(format!("[{nattrs}] {name}: {e}")),
            };
            let (x, y, tr, attrs, at, dt) = claimed;
            let verdict = run_mdoc_verifier(spec, circuits, x, y, tr, attrs, at, dt, &proof);
            if true_request {
                assert!(verdict.is_ok(), "[{nattrs}] the true request must verify");
            } else if verdict.is_ok() {
                accepted.push(format!("[{nattrs}] {name}"));
            }
        };
        let key = (pkx, pky);
        run("true request", honest, true);
        // Time outside the validity window.
        run(
            "now far in the past",
            req(key, honest_attrs, "1999-01-01T00:00:00Z", doc_type),
            false,
        );
        run(
            "now far in the future",
            req(key, honest_attrs, "2999-01-01T00:00:00Z", doc_type),
            false,
        );
        // The last attribute's value: last byte changed, a shorter and a
        // longer well-formed value, a value of another kind.
        for (what, edit) in [
            ("value last byte", 0usize),
            ("value shorter", 1),
            ("value longer", 2),
            ("value of another kind", 3),
        ] {
            let mut edited = honest_attrs.to_vec();
            let v = &mut edited[nattrs - 1].cbor_value;
            match edit {
                0 => *v.last_mut().unwrap() ^= 1,
                1 => {
                    // A text or byte string one byte shorter, header adjusted.
                    if v.len() >= 2 && (v[0] & 0x1f) >= 1 && (v[0] & 0x1f) < 24 {
                        v[0] -= 1;
                        v.pop();
                    } else {
                        *v = vec![0xf4];
                    }
                }
                2 => {
                    if (v[0] & 0x1f) < 23 && (v[0] >> 5 == 3 || v[0] >> 5 == 2) {
                        v[0] += 1;
                        v.push(b'x');
                    } else {
                        *v = vec![0x18, 0x2a];
                    }
                }
                _ => *v = if *v == [0xf5] { vec![0x01] } else { vec![0xf5] },
            }
            run(what, req(key, &edited, now, doc_type), false);
        }
        // The last attribute's identifier: another attribute of the
        // document, and identifiers the document lacks.
        let mut other_id = honest_attrs.to_vec();
        other_id[nattrs - 1].id = parsed.attrs[nattrs % parsed.attrs.len()].name.clone();
        if other_id[nattrs - 1].id == honest_attrs[nattrs - 1].id {
            other_id[nattrs - 1].id = b"family_name".to_vec();
        }
        run(
            "identifier of another attribute",
            req(key, &other_id, now, doc_type),
            false,
        );
        let mut flipped_id = honest_attrs.to_vec();
        *flipped_id[nattrs - 1].id.last_mut().unwrap() ^= 1;
        run(
            "identifier last byte",
            req(key, &flipped_id, now, doc_type),
            false,
        );
        let mut short_id = honest_attrs.to_vec();
        short_id[nattrs - 1].id.pop();
        run(
            "identifier shorter",
            req(key, &short_id, now, doc_type),
            false,
        );
        if nattrs == 2 {
            let mut swapped = honest_attrs.to_vec();
            let (a, b) = (swapped[0].cbor_value.clone(), swapped[1].cbor_value.clone());
            swapped[0].cbor_value = b;
            swapped[1].cbor_value = a;
            run(
                "values of the two attributes swapped",
                req(key, &swapped, now, doc_type),
                false,
            );
            let mut repeated = honest_attrs.to_vec();
            repeated[1] = repeated[0].clone();
            *repeated[1].cbor_value.last_mut().unwrap() ^= 1;
            run(
                "second attribute repeats the first with another value",
                req(key, &repeated, now, doc_type),
                false,
            );
        }
        // Document type and namespace.
        run(
            "document type last character",
            req(key, honest_attrs, now, "org.iso.18013.5.1.mDM"),
            false,
        );
        run(
            "document type shorter",
            req(key, honest_attrs, now, "org.iso.18013.5.1.mD"),
            false,
        );
        for (what, other) in [
            ("namespace last character", "org.iso.18013.5.2"),
            ("namespace is a proper prefix", "org.iso.18013.5"),
        ] {
            assert_ne!(other, ns);
            let other_ns: Vec<_> = honest_attrs
                .iter()
                .map(|a| req_attr(other, &a.id, &a.cbor_value))
                .collect();
            run(what, req(key, &other_ns, now, doc_type), false);
        }
        // Session transcript: another well-formed CBOR item.
        let mut tr = TEST_DATA.transcript.to_vec();
        *tr.last_mut().unwrap() ^= 1;
        if CborParser::new(&tr).parse_exact().is_err() {
            tr = vec![0x83, 0xf6, 0xf6, 0x01];
        }
        run(
            "another session transcript",
            (pkx, pky, &tr, honest_attrs, now, doc_type),
            false,
        );
        // Issuer key: the coordinates swapped, and x + 1.
        run(
            "issuer key coordinates swapped",
            (pky, pkx, TEST_DATA.transcript, honest_attrs, now, doc_type),
            false,
        );
        let mut x = num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le());
        x += 1u32;
        let x1 = format!("0x{}", x.to_str_radix(16));
        run(
            "issuer key x + 1",
            (&x1, pky, TEST_DATA.transcript, honest_attrs, now, doc_type),
            false,
        );
    }
    assert!(accepted.is_empty(), "false requests accepted: {accepted:?}");
    assert!(
        unproved.is_empty(),
        "false requests not proved: {unproved:?}"
    );
}
