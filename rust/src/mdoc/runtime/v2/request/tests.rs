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

//! The request checks and their early rejection in both roles, without
//! compiling a circuit.
use super::{Request, RequestError};
use crate::{
    mdoc::{
        circuits::cbor::encode_cbor_string,
        runtime::tests::specs::v2_spec,
        testcases::TEST_DATA,
        v2::{
            req_attr, run_mdoc_prover_inner, run_mdoc_verifier, MdocProverErrorCode,
            MdocVerifierErrorCode,
        },
    },
    runtime::{algebra::p256::P256Field, random::DeterministicRng},
};

/// A session transcript that is one CBOR item, the text string "inputs", so
/// that the early-rejection tests fail for the input they vary.
const SESSION: &[u8] = b"\x66inputs";

#[test]
fn session_transcript_must_be_one_cbor_item() {
    let spec = &v2_spec();
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let now = "2026-10-23T00:00:00Z";
    let valid = TEST_DATA.transcript;
    let mut two_items = valid.to_vec();
    two_items.extend_from_slice(valid);
    let mut trailing = valid.to_vec();
    trailing.push(0xff);
    let invalid: [&[u8]; 6] = [
        &[],
        &valid[..valid.len() - 1],
        &valid[..1],
        &two_items,
        &[0xf6, 0xf6],
        &trailing,
    ];
    for transcript in invalid {
        assert!(!super::session_transcript_is_one_item(transcript));
        let mut rng = DeterministicRng::new(42);
        // Deliberately invalid circuit and document bytes: validation must run first.
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                transcript,
                &attrs,
                now,
                "doc",
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput),
            "prover accepted session transcript {transcript:02x?}"
        );
        assert_eq!(rng.state, 42);
        assert_eq!(
            run_mdoc_verifier(spec, &[], "0", "0", transcript, &attrs, now, "doc", &[]),
            Err(MdocVerifierErrorCode::InvalidInput),
            "verifier accepted session transcript {transcript:02x?}"
        );
    }
    // A valid transcript passes the request check and reaches circuit loading.
    for transcript in [valid, SESSION, &[0xf6]] {
        assert!(super::session_transcript_is_one_item(transcript));
        let mut rng = DeterministicRng::new(42);
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                transcript,
                &attrs,
                now,
                "doc",
                &mut rng,
            ),
            Err(MdocProverErrorCode::CircuitParsingFailure)
        );
        assert_eq!(
            run_mdoc_verifier(spec, &[], "0", "0", transcript, &attrs, now, "doc", &[]),
            Err(MdocVerifierErrorCode::CircuitParsingFailure)
        );
    }
}

/// One request for the circuit-free error-table checks; each row changes
/// one field of a valid request.
#[derive(Clone)]
struct Fields {
    spec: crate::mdoc::v2::ZkSpecStruct,
    pkx: String,
    pky: String,
    transcript: Vec<u8>,
    attrs: Vec<crate::mdoc::v2::RequestedAttribute>,
    now: String,
    doc_type: String,
}
impl Fields {
    /// What `Request::check` says of these fields, and the codes both roles
    /// return when run with no circuits, no document and no proof, so a valid
    /// request stops at circuit loading. The prover must not draw randomness.
    fn codes(
        &self,
    ) -> (
        Option<RequestError>,
        MdocProverErrorCode,
        MdocVerifierErrorCode,
    ) {
        let checked = Request::check(
            &self.spec,
            &self.pkx,
            &self.pky,
            &self.transcript,
            &self.attrs,
            &self.now,
            &self.doc_type,
            &P256Field::new(),
        )
        .err();
        let mut rng = DeterministicRng::new(42);
        let prover = run_mdoc_prover_inner(
            &self.spec,
            &[],
            &[],
            &self.pkx,
            &self.pky,
            &self.transcript,
            &self.attrs,
            &self.now,
            &self.doc_type,
            &mut rng,
        )
        .unwrap_err();
        assert_eq!(rng.state, 42, "a rejected request consumed randomness");
        let verifier = run_mdoc_verifier(
            &self.spec,
            &[],
            &self.pkx,
            &self.pky,
            &self.transcript,
            &self.attrs,
            &self.now,
            &self.doc_type,
            &[],
        )
        .unwrap_err();
        (checked, prover, verifier)
    }
}

/// The request rows of the error table in `mdoc/runtime/v2/DESIGN.md`, in
/// both roles, with their numeric codes. A request failure gets the same code
/// in both roles, except the attribute count, which only the verifier names.
#[test]
fn request_errors_follow_the_error_table() {
    use MdocProverErrorCode as P;
    use MdocVerifierErrorCode as V;
    use RequestError as E;

    use crate::mdoc::proto::hash::constants::K_NAMESPACE_BYTES;
    let mut two = v2_spec();
    two.num_attributes = 2;
    let valid = Fields {
        spec: two,
        pkx: "0x1".into(),
        pky: "2".into(),
        transcript: SESSION.to_vec(),
        attrs: vec![
            req_attr("namespace", "a", [0xf5]),
            req_attr("namespace", "b", [0x01]),
        ],
        now: "2026-10-23T00:00:00Z".into(),
        doc_type: "doc".into(),
    };
    let with = |change: &dyn Fn(&mut Fields)| {
        let mut request = valid.clone();
        change(&mut request);
        request.codes()
    };
    // Archive or circuit rejected: the valid request reaches circuit loading.
    assert_eq!(
        valid.codes(),
        (None, P::CircuitParsingFailure, V::CircuitParsingFailure)
    );
    assert_eq!(
        (
            P::CircuitParsingFailure as u32,
            V::CircuitParsingFailure as u32
        ),
        (3, 1)
    );
    // Unsupported spec version.
    for version in [0, 7, 99] {
        assert_eq!(
            with(&|r| r.spec.version = version),
            (
                Some(E::Version),
                P::InvalidZkSpecVersion,
                V::InvalidZkSpecVersion
            )
        );
    }
    assert_eq!(
        (
            P::InvalidZkSpecVersion as u32,
            V::InvalidZkSpecVersion as u32
        ),
        (8, 10)
    );
    // Attribute count differs from the spec.
    for count in [0, 1, 3] {
        assert_eq!(
            with(&|r| r.attrs = vec![valid.attrs[0].clone(); count]),
            (
                Some(E::AttributeCount),
                P::InvalidInput,
                V::AttributeNumberMismatch
            )
        );
    }
    assert_eq!(
        (P::InvalidInput as u32, V::AttributeNumberMismatch as u32),
        (2, 9)
    );
    // Any other request-shape failure.
    let not_canonical = "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff";
    let shape: [(&str, &dyn Fn(&mut Fields)); 18] = [
        ("namespaces differ", &|r| {
            r.attrs[1].namespace_id = b"other".to_vec()
        }),
        ("empty namespace", &|r| {
            for a in &mut r.attrs {
                a.namespace_id.clear();
            }
        }),
        ("long namespace", &|r| {
            for a in &mut r.attrs {
                a.namespace_id = vec![b'n'; K_NAMESPACE_BYTES + 1];
            }
        }),
        ("non-UTF-8 namespace", &|r| {
            for a in &mut r.attrs {
                a.namespace_id = vec![0xff];
            }
        }),
        ("long identifier", &|r| r.attrs[0].id = vec![b'a'; 31]),
        ("long value", &|r| {
            r.attrs[1].cbor_value = encode_cbor_string(&[b'a'; 63]);
        }),
        ("empty document type", &|r| r.doc_type.clear()),
        ("long document type", &|r| r.doc_type = "x".repeat(33)),
        ("short time", &|r| r.now = "2026-10-23T00:00:00".into()),
        ("malformed time", &|r| r.now = "2026/10/23T00:00:00Z".into()),
        ("empty session transcript", &|r| r.transcript.clear()),
        ("two session transcript items", &|r| {
            r.transcript = vec![0xf6, 0xf6]
        }),
        ("truncated session transcript", &|r| {
            r.transcript.truncate(3)
        }),
        ("empty issuer key", &|r| r.pkx.clear()),
        ("bare 0x issuer key", &|r| r.pky = "0x".into()),
        ("non-hex issuer key", &|r| r.pkx = "0xg".into()),
        ("issuer key over 64 digits", &|r| {
            r.pky = format!("{}1", "0".repeat(64))
        }),
        ("non-canonical issuer key", &|r| {
            r.pkx = not_canonical.into()
        }),
    ];
    for (row, change) in shape {
        assert_eq!(
            with(change),
            (Some(E::Shape), P::InvalidInput, V::InvalidInput),
            "request-shape row: {row}"
        );
    }
    assert_eq!((P::InvalidInput as u32, V::InvalidInput as u32), (2, 7));
    // Unsupported attribute value.
    for value in [&[0x82, 0x01, 0x02][..], &[0x65, 0x61][..], &[0xf6][..]] {
        assert_eq!(
            with(&|r| r.attrs[0].cbor_value = value.to_vec()),
            (
                Some(E::UnsupportedAttribute),
                P::UnsupportedAttribute,
                V::UnsupportedAttribute
            )
        );
    }
    assert_eq!(
        (
            P::UnsupportedAttribute as u32,
            V::UnsupportedAttribute as u32
        ),
        (36, 11)
    );
}

#[test]
fn fixture_session_transcripts_are_single_cbor_items() {
    use crate::mdoc::testcases::ALL_TEST_CASES;
    assert!(super::session_transcript_is_one_item(TEST_DATA.transcript));
    for case in ALL_TEST_CASES {
        assert!(
            super::session_transcript_is_one_item(case.data.transcript),
            "{}",
            case.name
        );
    }
}

#[test]
fn namespace_capacity_and_encoding_are_checked_before_proving() {
    use crate::mdoc::proto::hash::constants::K_NAMESPACE_BYTES;
    let spec = &v2_spec();
    for namespace in [vec![], vec![b'n'; K_NAMESPACE_BYTES + 1], vec![0xff]] {
        let attrs = [req_attr(namespace, "a", [0xf5])];
        let mut rng = DeterministicRng::new(42);
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                SESSION,
                &attrs,
                "2026-10-23T00:00:00Z",
                "doc",
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput)
        );
        assert_eq!(rng.state, 42);
        assert_eq!(
            run_mdoc_verifier(
                spec,
                &[],
                "0",
                "0",
                SESSION,
                &attrs,
                "2026-10-23T00:00:00Z",
                "doc",
                &[],
            ),
            Err(MdocVerifierErrorCode::InvalidInput)
        );
    }
    assert!(super::public_inputs_fit(
        &[req_attr(vec![b'n'; K_NAMESPACE_BYTES], "a", [0xf5])],
        b"2026-10-23T00:00:00Z",
        b"doc",
    ));
}

#[test]
fn rejects_invalid_public_inputs_before_loading_or_sampling() {
    let spec = &v2_spec();
    let valid = req_attr("namespace", "a", [0xf5]);
    let now = "2026-10-23T00:00:00Z";
    let mut long_id = valid.clone();
    long_id.id = vec![b'a'; 31]; // CBOR header plus text exceeds the 32-byte slot.
    let mut long_value = valid.clone();
    long_value.cbor_value = encode_cbor_string(&[b'a'; 63]);
    let mut nested_value = valid.clone();
    nested_value.cbor_value = vec![0xc0; 100_000];
    nested_value.cbor_value.push(0x00);
    let long_doc = "x".repeat(33);
    let long_now = format!("{now}x");
    for (attrs, time, doc_type) in [
        (vec![], now, "doc"),
        (vec![valid.clone(), valid.clone()], now, "doc"),
        (vec![long_id], now, "doc"),
        (vec![long_value], now, "doc"),
        (vec![nested_value], now, "doc"),
        (vec![valid.clone()], &now[..19], "doc"),
        (vec![valid.clone()], long_now.as_str(), "doc"),
        (vec![valid.clone()], now, long_doc.as_str()),
    ] {
        let mut rng = DeterministicRng::new(42);
        // Deliberately invalid circuit and document bytes: validation must run first.
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                SESSION,
                &attrs,
                time,
                doc_type,
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput)
        );
        assert_eq!(
            rng.state, 42,
            "invalid inputs must not consume prover randomness"
        );
        let expected = if attrs.len() == spec.num_attributes {
            MdocVerifierErrorCode::InvalidInput
        } else {
            MdocVerifierErrorCode::AttributeNumberMismatch
        };
        assert_eq!(
            run_mdoc_verifier(spec, &[], "0", "0", SESSION, &attrs, time, doc_type, &[],),
            Err(expected)
        );
    }
    let boundary = req_attr("namespace", [b'a'; 30], encode_cbor_string(&[b'a'; 62]));
    assert!(super::public_inputs_fit(
        &[boundary],
        now.as_bytes(),
        &[b'x'; 32]
    ));
}

#[test]
fn utc_public_input_syntax_is_checked_and_case_is_normalized() {
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let canonical = b"2026-10-23T00:00:00Z";
    for (position, byte) in [
        (4, b'/'),
        (7, b'/'),
        (10, b'X'),
        (13, b'-'),
        (16, b'-'),
        (19, b'X'),
        (0, b'x'),
        (18, b'x'),
    ] {
        let mut bad = *canonical;
        bad[position] = byte;
        assert!(!super::public_inputs_fit(&attrs, &bad, b"doc"));
    }
    assert!(!super::public_inputs_fit(&attrs, canonical, b""));
    let expected = super::timestamp_digits(canonical).unwrap();
    for (t, z) in [(b'T', b'Z'), (b'T', b'z'), (b't', b'Z'), (b't', b'z')] {
        let mut time = *canonical;
        time[10] = t;
        time[19] = z;
        assert!(super::public_inputs_fit(&attrs, &time, b"doc"));
        assert_eq!(super::timestamp_digits(&time).unwrap(), expected);
    }
}
