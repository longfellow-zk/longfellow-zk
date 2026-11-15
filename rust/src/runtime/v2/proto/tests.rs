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

//! Longfellow v2 codec roundtrips and malformed-proof rejection.

use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::p256::P256Field,
        v2::proto::sumcheck::{RoundPoly, SumcheckProof, SumcheckProofGeometry},
    },
};

#[test]
fn single_hand_geometry_codec_and_malformed_shapes() {
    use crate::{core::algebra::SerializableField, runtime::v2::proto::sumcheck::LayerProof};
    let f = P256Field::new();
    let proof: SumcheckProof<4, _> = SumcheckProof {
        layers: vec![
            LayerProof {
                rounds: vec![
                    RoundPoly {
                        coefficients: [f.zero(), f.one()]
                    };
                    3
                ],
                cross: f.zero(),
                claims: [f.one(), f.zero()],
            },
            LayerProof {
                rounds: vec![],
                cross: f.zero(),
                claims: [f.zero(), f.one()],
            },
        ],
    };
    let geometry = proof.geometry();
    assert_eq!(geometry.serialized_elements().unwrap(), 12);
    let layout = geometry.pad_layout(7);
    assert_eq!(layout.layers[0].rounds[2], [11, 12]);
    assert_eq!(layout.layers[0].claims, [13, 14]);
    assert_eq!(layout.layers[1].claims, [17, 18]);
    let bytes = proof.write(&geometry, &f).unwrap();
    assert_eq!(bytes.len(), 12 * f.serialized_size_bytes());
    assert_eq!(
        SumcheckProof::read(&mut bytes.as_slice(), &geometry, &f).unwrap(),
        proof
    );
    for len in 0..bytes.len() {
        assert!(SumcheckProof::<4, _>::read(&mut &bytes[..len], &geometry, &f).is_err());
    }
    let invalid = SumcheckProofGeometry {
        logw_layers: vec![crate::runtime::v2::proto::sumcheck::MAX_LOGW + 1],
    };
    assert!(SumcheckProof::<4, _>::read(&mut bytes.as_slice(), &invalid, &f).is_err());
    let mut malformed = proof.clone();
    malformed.layers[0].rounds.pop();

    assert!(malformed.write(&geometry, &f).is_err());
}

#[test]
fn v2_codec_round_limit_is_inclusive_and_independent_of_host_width() {
    use crate::runtime::v2::proto::sumcheck::{pad_count, sane_logw, LayerProof, MAX_LOGW};
    let f = P256Field::new();
    for logw in [0, MAX_LOGW - 1, MAX_LOGW] {
        assert!(sane_logw(logw));
        let proof: SumcheckProof<4, _> = SumcheckProof {
            layers: vec![LayerProof {
                rounds: vec![
                    RoundPoly {
                        coefficients: [f.zero(), f.one()]
                    };
                    logw
                ],
                cross: f.zero(),
                claims: [f.one(), f.zero()],
            }],
        };
        let geometry = proof.geometry();
        assert_eq!(geometry.serialized_elements().unwrap(), 2 * logw + 3);
        let layout = geometry.pad_layout(7);
        assert_eq!(layout.layers[0].cross + 1, 7 + pad_count(logw));
        let bytes = proof.write(&geometry, &f).unwrap();
        let mut remaining = bytes.as_slice();
        assert_eq!(
            SumcheckProof::read(&mut remaining, &geometry, &f).unwrap(),
            proof
        );
        assert!(remaining.is_empty());
    }

    for logw in [MAX_LOGW + 1, usize::MAX] {
        assert!(!sane_logw(logw));
        let geometry = SumcheckProofGeometry {
            logw_layers: vec![logw],
        };
        assert!(geometry.serialized_elements().is_err());
        let input = [0u8; 32];
        let mut remaining = input.as_slice();
        assert!(SumcheckProof::<4, _>::read(&mut remaining, &geometry, &f).is_err());
        assert_eq!(remaining, input);
    }
    let too_many: SumcheckProof<4, _> = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![
                RoundPoly {
                    coefficients: [f.zero(), f.one()]
                };
                MAX_LOGW + 1
            ],
            cross: f.zero(),
            claims: [f.one(), f.zero()],
        }],
    };
    assert!(too_many.write(&too_many.geometry(), &f).is_err());
}

#[test]
fn sumcheck_rejects_aliases_in_every_field_position() {
    use fixtures::Aliased;

    use crate::runtime::algebra::gf2_128::Gf2_128Field;

    let f = Aliased(Gf2_128Field::new());
    // Include round coefficients, the cross coefficient and terminal claims,
    // both in an ordinary layer and a layer with no rounds.
    let geometry = SumcheckProofGeometry::new(vec![2, 0]);
    let count = geometry.serialized_elements().unwrap();
    let bytes: Vec<_> = (0..count).flat_map(|i| (i as u128).to_le_bytes()).collect();
    let mut remaining = bytes.as_slice();
    let proof = SumcheckProof::<2, _>::read(&mut remaining, &geometry, &f).unwrap();
    assert!(remaining.is_empty());
    assert_eq!(proof.write(&geometry, &f).unwrap(), bytes);

    for i in 0..count {
        let mut alias = bytes.clone();
        alias[16 * i..16 * (i + 1)].fill(0xff);
        assert!(
            SumcheckProof::<2, _>::read(&mut alias.as_slice(), &geometry, &f).is_err(),
            "alias at field position {i}"
        );
    }
}

#[test]
fn canonical_field_reader_rejects_without_consuming_input() {
    use std::io::ErrorKind;

    use super::{read_field, tests::fixtures::Aliased};
    use crate::{
        core::algebra::SerializableField,
        runtime::algebra::gf2_128::{Gf2_128, Gf2_128Field},
    };

    let f = Aliased(Gf2_128Field::new());
    let value = Gf2_128::from(42u128);
    let mut encoded = f.to_bytes(&value);
    encoded.extend_from_slice(&[7, 8, 9]);
    let mut remaining = encoded.as_slice();
    assert_eq!(read_field(&mut remaining, &f).unwrap(), value);
    assert_eq!(remaining, &[7, 8, 9]);

    for len in 0..16 {
        let input = &encoded[..len];
        let mut remaining = input;
        assert_eq!(
            read_field(&mut remaining, &f).unwrap_err().kind(),
            ErrorKind::UnexpectedEof
        );
        assert_eq!(remaining, input);
    }
    let alias = [0xff; 16];
    let mut remaining = alias.as_slice();
    assert_eq!(
        read_field(&mut remaining, &f).unwrap_err().kind(),
        ErrorKind::InvalidData
    );
    assert_eq!(remaining, alias);
}

mod polygero;
mod readers;

pub(super) mod fixtures;

/// Value kinds of the transcript grammar.
const B: u64 = 0;
const N: u64 = 1;
const E: u64 = 2;
const BITS: u64 = 3;
/// The registry's schema of every tag: its value kinds, and the counts the
/// schema fixes (`None` where the geometry sets the count).
fn schema(tag: u64) -> &'static [(u64, Option<u64>)] {
    match tag {
        16 => &[(B, None), (B, None), (B, Some(32)), (N, Some(2))],
        17 => &[(B, None), (B, None)],
        18 => &[(B, Some(32)), (N, None), (N, Some(3))],
        19 => &[(N, Some(4)), (B, None), (N, None), (N, None), (N, Some(2))],
        20 => &[(N, Some(4))],
        21 => &[(E, None)],
        22 => &[(B, None), (N, Some(3)), (N, None)],
        32 => &[(B, Some(32))],
        33 => &[(E, Some(2))],
        48 => &[(E, Some(2))],
        49 => &[(E, Some(1))],
        50 => &[(E, Some(2))],
        64 => &[(E, Some(1))],
        65 => &[(BITS, None), (BITS, None)],
        80 => &[(E, None)],
        81 => &[(E, Some(1))],
        96 => &[(E, None), (E, None)],
        112 => &[(B, None)],
        _ => panic!("tag {tag} is not in the registry"),
    }
}

/// Check a complete proof's trace against the registry and its wire bytes:
/// every message has its tag's schema and each tag keeps one exact list of
/// value counts where the geometry is fixed per field (transcript I6); the
/// statement precedes every prover message (I1); the prover messages'
/// payloads, in send order and without headers, are the interactive section
/// `proof[start..end]` (proto I4, I5); the last message is the seal over
/// every byte before the seal block (I10).
pub(crate) fn check_trace_matches_wire(
    trace: &crate::runtime::v2::transcript::Trace,
    proof: &[u8],
    start: usize,
    end: usize,
) {
    let mut payload = Vec::new();
    let mut prover = false;
    let messages: Vec<_> = trace.messages().collect();
    for m in &messages {
        let expected = schema(m.tag);
        assert_eq!(m.schema.len(), expected.len(), "tag {} arity", m.tag);
        for (&(kind, count), &(want, fixed)) in m.schema.iter().zip(expected) {
            assert_eq!(kind, want, "tag {} kind", m.tag);
            if let Some(want_count) = fixed {
                assert_eq!(count, want_count, "tag {} count", m.tag);
            }
        }
        match m.tag {
            16..=31 => assert!(
                !prover,
                "statement message {} after a prover message",
                m.tag
            ),
            112 => {}
            _ => {
                prover = true;
                payload.extend_from_slice(&m.payload);
            }
        }
    }
    assert_eq!(payload.len(), end - start, "interactive section length");
    assert!(
        payload == proof[start..end],
        "wire bytes differ from absorbed payloads"
    );
    let seal = messages.last().unwrap();
    assert_eq!(seal.tag, 112);
    assert!(seal.payload == proof[..proof.len() - 32]);
    assert_eq!(
        messages.iter().filter(|m| m.tag == 112).count(),
        1,
        "one seal"
    );
}

/// The registry name of a tag, for decoded vectors.
fn tag_name(tag: u64) -> &'static str {
    match tag {
        16 => "MdocStatement",
        17 => "ZkStatement",
        18 => "Circuit",
        19 => "CommitmentLayout",
        20 => "JointGeometry",
        21 => "PublicInputs",
        22 => "AdapterLayout",
        32 => "Commitment",
        33 => "FingerprintResponse",
        48 => "SumcheckRound",
        49 => "SumcheckCross",
        50 => "SumcheckClaims",
        64 => "SplitOpening",
        65 => "P256AdapterQuotients",
        80 => "PackingU",
        81 => "PackingA",
        96 => "PolygeroResponse",
        112 => "Seal",
        _ => panic!("tag {tag} is not in the registry"),
    }
}

/// Decode one strand node's SHA-256 preimage with the transcript grammar and
/// the registry alone, one line per header, value and terminator, and check
/// that the node is consumed exactly. Integers are decimal; bytes, elements
/// and packed bits are lowercase hex (elements in their canonical
/// encodings, `width` bytes each, from the FieldID: 16 for GF(2^128), 32 for
/// P-256).
pub(crate) fn describe_node(node: &[u8]) -> String {
    use std::fmt::Write;
    let mut at = 0;
    let mut take = |n: usize| {
        let s = &node[at..at + n];
        at += n;
        s
    };
    let u32_at = |b: &[u8]| u32::from_le_bytes(b.try_into().unwrap());
    let u64_at = |b: &[u8]| u64::from_le_bytes(b.try_into().unwrap());
    let mut out = String::new();
    let kind = u32_at(take(4));
    let id = u64_at(take(8));
    let parents = u32_at(take(4));
    writeln!(
        out,
        "header: u32 STRAND={kind}, u64 id={id}, u32 parents={parents}"
    )
    .unwrap();
    assert_eq!(kind, 1);
    if parents == 1 {
        writeln!(out, "  parent digest: {}", hex::encode(take(32))).unwrap();
    }
    loop {
        let word = u64_at(take(8));
        if word < 16 {
            let end = match word {
                0 => "ROUND (a draw follows)",
                1 => "SEAL (the proof ends)",
                _ => panic!("reserved terminator {word}"),
            };
            writeln!(out, "terminator: u64 {word} = {end}").unwrap();
            break;
        }
        writeln!(out, "message: u64 tag={word} {}", tag_name(word)).unwrap();
        for (i, &(want, _)) in schema(word).iter().enumerate() {
            let k = u64_at(take(8));
            assert_eq!(k, want, "tag {word} value {i} kind");
            match k {
                B => {
                    let n = u64_at(take(8)) as usize;
                    writeln!(
                        out,
                        "  value {i}: u64 kind=0 Bytes, u64 count={n}: {}",
                        hex::encode(take(n))
                    )
                    .unwrap();
                }
                N => {
                    let n = u64_at(take(8)) as usize;
                    let xs: Vec<String> = (0..n).map(|_| u64_at(take(8)).to_string()).collect();
                    writeln!(
                        out,
                        "  value {i}: u64 kind=1 Nats, u64 count={n}: [{}]",
                        xs.join(", ")
                    )
                    .unwrap();
                }
                E => {
                    let field = u64_at(take(8));
                    let n = u64_at(take(8)) as usize;
                    let width = match field {
                        1 => 32,
                        4 => 16,
                        _ => panic!("field {field} has no known width"),
                    };
                    let xs: Vec<String> = (0..n).map(|_| hex::encode(take(width))).collect();
                    writeln!(
                        out,
                        "  value {i}: u64 kind=2 Elements, u64 field={field} ({}), u64 count={n}: [{}]",
                        if field == 1 { "P256" } else { "GF2_128" },
                        xs.join(", ")
                    )
                    .unwrap();
                }
                BITS => {
                    let n = u64_at(take(8)) as usize;
                    writeln!(
                        out,
                        "  value {i}: u64 kind=3 Bits, u64 count={n}: {} (least significant bit first)",
                        hex::encode(take(n.div_ceil(8)))
                    )
                    .unwrap();
                }
                _ => unreachable!(),
            }
        }
    }
    assert_eq!(at, node.len(), "node consumed exactly");
    out
}

/// Append `text` to the file named by `LONGFELLOW_TRANSCRIPT_VECTORS`, if
/// set. The tests pin the vectors' digests; this only exports them.
pub(crate) fn export_vectors(text: &str) {
    if let Ok(path) = std::env::var("LONGFELLOW_TRANSCRIPT_VECTORS") {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();
        file.write_all(text.as_bytes()).unwrap();
    }
}

/// A node's bytes and its decoding, for `export_vectors`.
pub(crate) fn node_vector(title: &str, index: usize, node: &[u8]) -> String {
    format!(
        "### {title}, node {index}: {} bytes, SHA-256 {}\nhex: {}\n{}\n",
        node.len(),
        hex::encode(<sha2::Sha256 as sha2::Digest>::digest(node)),
        hex::encode(node),
        describe_node(node)
    )
}
