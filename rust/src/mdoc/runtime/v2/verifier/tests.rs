// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc statement holds every value the mdoc verifier uses (transcript
//! I1, I3).
//!
//! `run_mdoc_verifier` hands the session it opened to `observe` before it
//! reads a proof byte. When a test has armed it, `observe` decodes the
//! statement from the bytes the session hashed and checks it against the
//! statement object and geometry the verifier reads from that session.
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

use crate::{
    compile::algebra::CompileNat,
    core::{algebra::Nat, proto::v2::Circuit},
    mdoc::{
        circuits::cbor::test_utils::parse_test_data,
        development_provider::compile_next,
        testcases::TEST_DATA,
        v2::{
            decompress_circuits,
            inputs::PublicInputs,
            link, proof_geometry,
            provider::ProvidedCircuit,
            req_attr,
            request::Request,
            run_mdoc_verifier,
            transcript::{Identity, MdocStatement, PROTOCOL_ID},
            MdocProof, MdocVerifierErrorCode, PolygeroParameters, RequestedAttribute, ZkSpecStruct,
        },
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, EvaluationDomain,
                QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        random::DeterministicRng,
        v2::{
            proto::{
                tags::Tag,
                tests::{
                    messages::{check_absorbed, sent},
                    statement::{self, Statement as Decoded},
                },
            },
            transcript::{
                EncodedProof, Opened, Statement, Trace, Transcript, VerifiedProof, SEAL_BYTES,
            },
        },
    },
};

thread_local! {
    /// While armed, the statement bytes of every session `run_mdoc_verifier`
    /// opened on this thread, each checked by `observe`.
    static OBSERVED: RefCell<Option<Vec<Vec<u8>>>> = const { RefCell::new(None) };
}

/// The test hook of `run_mdoc_verifier`, called on the session it opened.
/// When armed, decode the statement the session absorbed and check every
/// value the verifier reads against it: the mdoc identity here, the
/// composition through `ComposedStatement::check_absorbed_for_test`, and
/// the geometry the proof is parsed against, which must be the statement's.
pub(super) fn observe<DH, DS>(session: &mut Opened<'_, MdocStatement<'_, DH, DS>>)
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    if OBSERVED.with_borrow(Option::is_none) {
        return;
    }
    let bytes = session.statement_bytes_for_test().to_vec();
    let d = Decoded::from_statement_bytes(&bytes);
    let used = session.statement();
    assert!(std::ptr::eq(session.geometry().part(), used.geometry()));
    let (transcript, spec) = Statement::identity(used).fields_for_test();
    let ZkSpecStruct {
        combined_hash,
        num_attributes,
        version,
        polygero,
    } = spec;
    let PolygeroParameters { k, n, s, t } = *polygero;
    let identity = statement::Identity::Mdoc {
        protocol: PROTOCOL_ID.to_vec(),
        session: transcript.to_vec(),
        combined_hash: *combined_hash,
        version: *version as u64,
        attributes: *num_attributes as u64,
    };
    assert_eq!(d.identity, identity, "mdoc identity");
    assert_eq!(
        d.joint,
        [k, s, n, t].map(|x| x as u64),
        "the spec's profile"
    );
    // The circuits' public input counts follow from the attribute count.
    let counts = d.public.iter().map(|p| p.elements.len());
    assert!(counts.eq([901 + 788 * num_attributes, 258]));
    used.check_absorbed_for_test(&d, |mode| mode.check_absorbed_for_test(&d));
    OBSERVED.with_borrow_mut(|o| o.as_mut().unwrap().push(bytes));
}

/// Run `f` with the observer armed; return its result and the statement
/// bytes of every session the verifier opened meanwhile.
fn observed<T>(f: impl FnOnce() -> T) -> (T, Vec<Vec<u8>>) {
    OBSERVED.set(Some(Vec::new()));
    let out = f();
    (out, OBSERVED.take().unwrap())
}

/// Compiling a NEXT circuit takes about 1.5 GB at its peak. The tests here
/// compile one circuit at a time, so that together they add at most one
/// compilation to the peak memory of the test run.
static COMPILING: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// One NEXT circuit and the test request for its attribute count: the
/// first attributes of `TEST_DATA`, repeated as needed.
pub(super) struct Fixture {
    provided: ProvidedCircuit,
    attrs: Vec<RequestedAttribute>,
    pkx: String,
    pky: String,
    now: &'static str,
}
const DOC_TYPE: &str = "org.iso.18013.5.1.mDL";
impl Fixture {
    pub(super) fn new(count: usize) -> Self {
        let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
        let coordinate = |value: &CompileNat<4>| {
            format!(
                "0x{}",
                num_bigint::BigUint::from_bytes_le(&value.to_bytes_le()).to_str_radix(16)
            )
        };
        let attrs = parsed
            .attrs
            .iter()
            .cycle()
            .take(count)
            .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
            .collect();
        let provided = {
            let _one = COMPILING
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            compile_next(count).unwrap()
        };
        Self {
            provided,
            attrs,
            pkx: coordinate(&issuer_pk.0),
            pky: coordinate(&issuer_pk.1),
            now,
        }
    }
    pub(super) fn prove(&self) -> EncodedProof {
        super::super::run_mdoc_prover_encoded(
            self.provided.spec(),
            self.provided.compressed(),
            TEST_DATA.mdoc,
            &self.pkx,
            &self.pky,
            TEST_DATA.transcript,
            &self.attrs,
            self.now,
            DOC_TYPE,
            &mut DeterministicRng::new(42),
        )
        .unwrap()
    }
    pub(super) fn verify(&self, proof: &[u8]) -> Result<VerifiedProof, MdocVerifierErrorCode> {
        run_mdoc_verifier(
            self.provided.spec(),
            self.provided.compressed(),
            &self.pkx,
            &self.pky,
            TEST_DATA.transcript,
            &self.attrs,
            self.now,
            DOC_TYPE,
            proof,
        )
    }
}

/// The statement of every mdoc shape (one to four attributes), decoded from
/// the bytes the verifier hashed, holds every value the verifier uses; and
/// it is exactly the start of the first node of the complete verification's
/// trace, which holds it once.
#[test]
fn mdoc_statement_round_trip() {
    std::thread::scope(|scope| {
        let tasks: Vec<_> = (1..=4)
            .map(|count| {
                scope.spawn(move || {
                    let fixture = Fixture::new(count);
                    let proof = fixture.prove();
                    let (result, opened) = observed(|| fixture.verify(proof.as_bytes()));
                    let verified = result.unwrap();
                    let [bytes] = &opened[..] else {
                        panic!("the verifier opens one session")
                    };
                    let trace = &verified.trace;
                    assert!(trace.nodes[0].starts_with(bytes), "{count} attributes");
                    assert_eq!(
                        Decoded::from_trace(trace),
                        Decoded::from_statement_bytes(bytes)
                    );
                })
            })
            .collect();
        for task in tasks {
            task.join().unwrap();
        }
    });
}

/// The statement bytes of the session `run_mdoc_verifier` opens for
/// `fixture`'s request, built the way it builds them, but with the identity's
/// session transcript `session` and with `spec` for the identity and the
/// composition. The public inputs stay the request's.
fn mdoc_statement_bytes(
    fixture: &Fixture,
    (signature, hash): (&Circuit<P256Field>, &Circuit<Gf2_128Field>),
    session: &[u8],
    spec: &ZkSpecStruct,
) -> Vec<u8> {
    let p256 = P256Field::new();
    let p256_2 = Fp2Field::new(&p256);
    let signature_domain = QuadraticExtensionFftInterpolatorFactory::new(
        &p256,
        &p256_2,
        p256_2.omega(),
        p256_2.omega_order(),
    );
    let gf2 = Gf2_128Field::new();
    let hash_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let request = Request::check(
        fixture.provided.spec(),
        &fixture.pkx,
        &fixture.pky,
        TEST_DATA.transcript,
        &fixture.attrs,
        fixture.now,
        DOC_TYPE,
        &p256,
    )
    .unwrap();
    let public = PublicInputs::derive(&request, &p256);
    let composition =
        link::composition(spec, signature, hash, (&hash_domain, &signature_domain)).unwrap();
    let statement = composition
        .statement(
            Identity::for_test(session, spec),
            public.hash(),
            public.signature(),
        )
        .unwrap();
    Opened::new(&statement).statement_bytes_for_test().to_vec()
}

/// One-field sensitivity of the mdoc identity and spec (transcript I1): a
/// statement built with one value changed has other bytes. The patterns
/// are exhaustive, so a new field does not compile until it is covered.
#[test]
fn mdoc_identity_fields_are_absorbed() {
    let fixture = Fixture::new(1);
    let circuits = decompress_circuits(
        fixture.provided.compressed(),
        &P256Field::new(),
        &Gf2_128Field::new(),
    )
    .unwrap();
    let spec = *fixture.provided.spec();
    let identity = Identity::for_test(TEST_DATA.transcript, &spec);
    let (transcript, _) = identity.fields_for_test();
    let bytes = |session: &[u8], changed: &ZkSpecStruct| {
        mdoc_statement_bytes(&fixture, (&circuits.0, &circuits.1), session, changed)
    };
    let base = bytes(transcript, &spec);
    // The builder writes the statement the verifier opens: the observer sees
    // it before the empty proof fails to parse.
    let (result, opened) = observed(|| fixture.verify(&[]));
    assert_eq!(
        result.err(),
        Some(MdocVerifierErrorCode::HashParsingFailure)
    );
    assert_eq!(opened, std::slice::from_ref(&base));
    // The session transcript, written whole: its first, middle and last
    // bytes, and its length.
    let n = transcript.len();
    for i in [0, n / 2, n - 1] {
        let mut changed = transcript.to_vec();
        changed[i] ^= 1;
        assert_ne!(bytes(&changed, &spec), base, "session byte {i}");
    }
    assert_ne!(bytes(&transcript[..n - 1], &spec), base, "session length");
    // The spec.
    let ZkSpecStruct {
        combined_hash,
        num_attributes,
        version,
        polygero,
    } = spec;
    // The combined hash, written whole: each byte.
    for i in 0..32 {
        let mut changed = combined_hash;
        changed[i] ^= 1;
        let other = ZkSpecStruct {
            combined_hash: changed,
            ..spec
        };
        assert_ne!(bytes(transcript, &other), base, "combined hash byte {i}");
    }
    // The attribute count and the version, written. Neither changes the
    // composition; the request check rejects either for these circuits.
    let more = ZkSpecStruct {
        num_attributes: num_attributes + 1,
        ..spec
    };
    assert_ne!(bytes(transcript, &more), base, "attribute count");
    let later = ZkSpecStruct {
        version: version + 1,
        ..spec
    };
    assert_ne!(bytes(transcript, &later), base, "version");
    // The profile, written in `JointGeometry`: each value.
    let PolygeroParameters {
        k,
        n: columns,
        s,
        t,
    } = polygero;
    for (name, changed) in [
        (
            "k",
            PolygeroParameters {
                k: k + 1,
                ..polygero
            },
        ),
        (
            "n",
            PolygeroParameters {
                n: columns + 1,
                ..polygero
            },
        ),
        (
            "s",
            PolygeroParameters {
                s: s + 1,
                ..polygero
            },
        ),
        (
            "t",
            PolygeroParameters {
                t: t + 1,
                ..polygero
            },
        ),
    ] {
        let other = ZkSpecStruct {
            polygero: changed,
            ..spec
        };
        assert_ne!(bytes(transcript, &other), base, "profile {name}");
    }
}

/// Alter prover messages of the 1-attribute proof, one byte each where the
/// proof carries it: the first and the last occurrence of each tag in each
/// field (payload widths tell the fields apart). Each is absorbed as altered
/// before the next draw, which changes, and the proof is rejected; see
/// `proto::tests::messages`.
#[test]
fn mdoc_prover_messages_are_absorbed() {
    let fixture = Fixture::new(1);
    let proof = fixture.prove();
    let verified = fixture.verify(proof.as_bytes()).unwrap();
    let honest = &verified.trace;
    let messages = sent(honest, 4);
    let mut ends: BTreeMap<(u64, usize), [usize; 2]> = BTreeMap::new();
    for (i, m) in messages.iter().enumerate() {
        ends.entry((m.tag, m.len)).or_insert([i, i])[1] = i;
    }
    let tags: BTreeSet<u64> = ends.keys().map(|&(tag, _)| tag).collect();
    let expected = [
        Tag::Commitment,
        Tag::FingerprintResponse,
        Tag::SumcheckRound,
        Tag::SumcheckCross,
        Tag::SumcheckClaims,
        Tag::SplitOpening,
        Tag::P256AdapterQuotients,
        Tag::PackingU,
        Tag::PackingA,
        Tag::PolygeroResponse,
    ];
    assert_eq!(tags, expected.map(Tag::value).into());
    let chosen: BTreeSet<usize> = ends.values().flatten().copied().collect();
    let verify = |altered: &[u8]| {
        let (result, traces) = Trace::dropped(|| fixture.verify(altered));
        (result.is_ok(), traces)
    };
    for &i in &chosen {
        check_absorbed(honest, proof.as_bytes(), &messages[i], &verify);
    }
}

/// The field regions of a complete 1-attribute proof, in proof order: the
/// magic; each interactive field of the body, from `trace` (a field's
/// consecutive sumcheck messages form one region, as do its packing
/// messages); each field's opened rows; the nonces; the frontier's count
/// and its digests; the seal block. They tile the proof.
fn regions(fixture: &Fixture, bytes: &[u8], trace: &Trace) -> Vec<(String, Range<usize>)> {
    let mut out = vec![("magic".to_string(), 0..4)];
    for m in sent(trace, 4) {
        let tag = Tag::from_value(m.tag).unwrap();
        let name = match tag {
            Tag::SumcheckRound | Tag::SumcheckCross | Tag::SumcheckClaims => "sumcheck".into(),
            Tag::PackingU | Tag::PackingA => "packing".into(),
            _ => format!("{tag:?}"),
        };
        let grouped = matches!(name.as_str(), "sumcheck" | "packing");
        match out.last_mut() {
            Some((last, range)) if grouped && *last == name && range.end == m.offset => {
                range.end += m.len;
            }
            _ => out.push((name, m.offset..m.offset + m.len)),
        }
    }
    let (gf2, p256) = (Gf2_128Field::new(), P256Field::new());
    let (signature, hash) =
        decompress_circuits(fixture.provided.compressed(), &p256, &gf2).unwrap();
    let geometry = proof_geometry(fixture.provided.spec(), &signature, &hash).unwrap();
    let mut session = Transcript::for_test(b"regions");
    let decoded = MdocProof::read(bytes, &session.bound(&geometry.body), &gf2, &p256).unwrap();
    let polygero = &decoded.body.polygero;
    let (nonces, frontier) = polygero.authentication_bytes();
    let terminal = [
        ("host rows", 16 * polygero.bodies().0.rows.len()),
        ("split rows", 32 * polygero.bodies().1 .0.rows.len()),
        ("nonces", nonces),
        ("frontier count", 8),
        ("frontier", frontier - 8),
        ("seal", SEAL_BYTES),
    ];
    for (name, len) in terminal {
        let start = out.last().unwrap().1.end;
        out.push((name.into(), start..start + len));
    }
    for pair in out.windows(2) {
        assert_eq!(
            pair[0].1.end, pair[1].1.start,
            "{} then {}",
            pair[0].0, pair[1].0
        );
    }
    assert_eq!(
        out.last().unwrap().1.end,
        bytes.len(),
        "the regions tile the proof"
    );
    out
}

/// Flip one byte of the complete 1-attribute proof at the start, middle and
/// end of every field region of the body and the seal, and at 200
/// pseudo-random positions with pseudo-random masks: the complete verifier
/// rejects every flip.
#[test]
fn mdoc_byte_flips_are_rejected() {
    let fixture = Fixture::new(1);
    let proof = fixture.prove();
    let bytes = proof.as_bytes();
    let verified = fixture.verify(bytes).unwrap();
    let mut flips: Vec<(usize, u8)> = Vec::new();
    for (_, range) in regions(&fixture, bytes, &verified.trace) {
        for i in [range.start, range.start + range.len() / 2, range.end - 1] {
            if !flips.contains(&(i, 1)) {
                flips.push((i, 1));
            }
        }
    }
    // SplitMix64 from a fixed seed: positions and nonzero masks.
    let mut state = 0x6c66_7a6b_7632_7478_u64;
    for _ in 0..200 {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^= z >> 31;
        let position = (z % bytes.len() as u64) as usize;
        flips.push((position, ((z >> 56) as u8).max(1)));
    }
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get().min(8));
    let accepted: Vec<(usize, u8)> = std::thread::scope(|scope| {
        let tasks: Vec<_> = flips
            .chunks(flips.len().div_ceil(threads))
            .map(|chunk| {
                let shared = &fixture;
                scope.spawn(move || {
                    chunk
                        .iter()
                        .filter(|&&(i, mask)| {
                            let mut flipped = bytes.to_vec();
                            flipped[i] ^= mask;
                            shared.verify(&flipped).is_ok()
                        })
                        .copied()
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        tasks.into_iter().flat_map(|t| t.join().unwrap()).collect()
    });
    assert_eq!(flips.len(), 251);
    assert!(accepted.is_empty(), "accepted flips: {accepted:?}");
}

mod false_requests;
