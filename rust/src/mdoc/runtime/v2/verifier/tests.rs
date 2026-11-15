// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc statement holds every value the mdoc verifier uses (transcript
//! I1, I3).
//!
//! `run_mdoc_verifier` hands the session it opened to `observe` before it
//! reads a proof byte. When a test has armed it, `observe` decodes the
//! statement from the bytes the session hashed and checks it against the
//! statement object and geometry the verifier reads from that session.
use std::cell::RefCell;

use crate::{
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        circuits::cbor::test_utils::parse_test_data,
        development_provider::compile_next,
        testcases::TEST_DATA,
        v2::{
            provider::ProvidedCircuit,
            req_attr, run_mdoc_verifier,
            transcript::{MdocStatement, PROTOCOL_ID},
            MdocVerifierErrorCode, PolygeroParameters, RequestedAttribute, ZkSpecStruct,
        },
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
        random::DeterministicRng,
        v2::{
            proto::tests::statement::{self, Statement as Decoded},
            transcript::{EncodedProof, Opened, Statement, VerifiedProof},
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
        Self {
            provided: compile_next(count).unwrap(),
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
