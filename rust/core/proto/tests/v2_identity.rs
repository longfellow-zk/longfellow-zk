// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::{Digest, Sha256};

use super::{compute_id, id_bytes};
use crate::core::{
    algebra::{AlgebraicField, SerializableField},
    proto::v2::{Constant, Layer, Linear, Quadratic, RawCircuit, RawCircuitBuilder, Stream},
};

fn fixture<F: SerializableField + AlgebraicField>(f: &F) -> RawCircuit<F> {
    RawCircuitBuilder {
        ninput: 4,
        npublic_input: 1,
        noutput: 2,
        logv: 1,
        constants: vec![f.one(), f.one()],
        layers: vec![Layer::with_assertions(
            4,
            Stream {
                deltas: vec![
                    Quadratic {
                        g: 0,
                        l: 1,
                        r: 2,
                        k: 0,
                    },
                    Quadratic {
                        g: 1,
                        l: 0,
                        r: 0,
                        k: 1,
                    },
                ],
                segments: vec![vec![0, 1], vec![0]].into(),
                tokens: vec![0],
            },
            Stream::<Linear>::from_terms([Linear { g: 0, l: 3, k: 1 }]),
            Stream::<Constant>::from_terms([Constant { g: 1, k: 0 }]),
            |_| false,
        )],
    }
    .build()
}
fn reference<F: SerializableField + AlgebraicField>(f: &F) -> Vec<u8> {
    let mut b = b"LFC3-v2-segmented-id-v2".to_vec();
    for n in [usize::from(f.is_binary()), f.serialized_size_bytes()] {
        b.extend((n as u64).to_le_bytes());
    }
    b.extend(f.serialized_mone());
    for n in [2u64, 1, 4, 1, 1, 2] {
        b.extend(n.to_le_bytes());
    }
    b.extend(f.to_bytes(&f.one()));
    b.extend(f.to_bytes(&f.one()));
    for n in [4u64, 2] {
        b.extend(n.to_le_bytes());
    }
    for (tag, counts, words) in [
        (
            0u64,
            [2u64, 2, 3, 1],
            vec![0u64, 1, 2, 0, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0],
        ),
        (1u64, [1u64, 1, 1, 1], vec![0u64, 3, 1, 1, 0, 0]),
        (2u64, [1u64, 1, 1, 1], vec![1u64, 0, 1, 0, 0]),
    ] {
        b.extend(tag.to_le_bytes());
        for n in counts {
            b.extend(n.to_le_bytes());
        }
        for n in words {
            b.extend(n.to_le_bytes());
        }
    }
    b
}
fn check<F: SerializableField + AlgebraicField>(f: &F) {
    let raw = fixture(f);
    let expected = reference(f);
    assert_eq!(id_bytes(f, &raw), expected);
    assert_eq!(
        compute_id(f, &raw),
        <[u8; 32]>::from(Sha256::digest(&expected))
    );
    let original = compute_id(f, &raw);
    // Shared fixed vectors run unchanged on native 32-bit and 64-bit targets.
    let golden = if f.is_binary() {
        "c1087aada076a12f2f00242b65d12020ea14d5417c2b7e5d95ca2701866d8a81"
    } else {
        "2b7488ec97900bcff2d3bae5d295f16efda174fc6a507065e316570346d84fa4"
    };
    assert_eq!(hex::encode(original), golden);
    {
        use crate::core::proto::{
            v2::{Circuit, CircuitReader, CircuitWriter},
            FieldID,
        };
        let circuit = Circuit::from_raw(f, raw);
        let writer = CircuitWriter::new(f, FieldID::None);
        let bytes = writer.to_bytes(&circuit);
        let reader = CircuitReader::new(f, FieldID::None);
        let (decoded, tail) = reader.from_bytes(&bytes).unwrap();
        assert!(tail.is_empty());
        assert_eq!(compute_id(f, &decoded.raw), original);
        assert_eq!(decoded.id, circuit.id);
        assert_eq!(writer.to_bytes(&decoded), bytes);
        assert_eq!(id_bytes(f, &decoded.raw), id_bytes(f, &circuit.raw));
        let mut input = std::io::BufReader::with_capacity(1, bytes.as_slice());
        let streamed = reader.from_stream(&mut input).unwrap();
        assert_eq!(compute_id(f, &streamed.raw), original);
        assert_eq!(writer.to_bytes(&streamed), bytes);
    }
    let edits: Vec<Box<dyn Fn(&mut RawCircuitBuilder<F>)>> = vec![
        Box::new(|r| r.ninput += 1),
        Box::new(|r| r.npublic_input += 1),
        Box::new(|r| r.noutput += 1),
        Box::new(|r| r.logv += 1),
        Box::new(|r| r.constants.push(r.constants[0].clone())),
        Box::new(|r| r.layers[0].nw += 1),
        Box::new(|r| r.layers[0].logw += 1),
        Box::new(|r| r.layers[0].quadratic.deltas[0].g += 1),
        Box::new(|r| r.layers[0].quadratic.deltas[0].l += 1),
        Box::new(|r| r.layers[0].quadratic.deltas[0].r += 1),
        Box::new(|r| r.layers[0].quadratic.deltas[0].k = 1),
        Box::new(|r| r.layers[0].linear.deltas[0].l -= 1),
        Box::new(|r| r.layers[0].constant.deltas[0].k = 1),
        Box::new(|r| r.layers[0].quadratic.segments[0][0] = 1),
        Box::new(|r| r.layers[0].quadratic.segments = vec![vec![0], vec![1, 0]].into()),
        Box::new(|r| r.layers[0].quadratic.tokens.push(1)),
        // The second segment is unused, but still authenticated.
        Box::new(|r| r.layers[0].quadratic.segments[1][0] = 1),
    ];
    for (i, edit) in edits.into_iter().enumerate() {
        let mut changed = fixture(f).into_builder();
        edit(&mut changed);
        assert_ne!(original, compute_id(f, &changed.build()), "mutation {i}");
    }
    let mut changed = fixture(f).into_builder();
    changed.constants[0] = f.zero();
    assert_ne!(original, compute_id(f, &changed.build()));

    #[cfg(feature = "compiler")]
    {
        let raw = fixture(f);
        let mut quadratic = Vec::new();
        let mut linear = Vec::new();
        let mut constant = Vec::new();
        raw.layers[0]
            .quadratic
            .for_each(|t| quadratic.push((t.g, t.l, t.r, raw.constants[t.k as usize].clone())));
        raw.layers[0]
            .linear
            .for_each(|t| linear.push((t.g, t.l, raw.constants[t.k as usize].clone())));
        raw.layers[0]
            .constant
            .for_each(|t| constant.push((t.g, raw.constants[t.k as usize].clone())));
        let circuit = crate::compile::compiler::segment_circuit_v2(f, raw);
        assert_ne!(circuit.id, original);
        let mut got = Vec::new();
        circuit.raw.layers[0]
            .quadratic
            .for_each(|t| got.push((t.g, t.l, t.r, circuit.raw.constants[t.k as usize].clone())));
        assert_eq!(got, quadratic);
        let mut got = Vec::new();
        circuit.raw.layers[0]
            .linear
            .for_each(|t| got.push((t.g, t.l, circuit.raw.constants[t.k as usize].clone())));
        assert_eq!(got, linear);
        let mut got = Vec::new();
        circuit.raw.layers[0]
            .constant
            .for_each(|t| got.push((t.g, circuit.raw.constants[t.k as usize].clone())));
        assert_eq!(got, constant);
    }
}
#[test]
fn segmented_identity_binary() {
    check(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}
#[test]
fn segmented_identity_prime() {
    check(&crate::runtime::algebra::p256::P256Field::new());
}

#[test]
fn identity_hashes_stored_arrays_without_expanding_tokens() {
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let mut raw = fixture(&f).into_builder();
    raw.layers[0].quadratic.segments = vec![vec![0; 65536]].into();
    raw.layers[0].quadratic.tokens = vec![0; 65536];
    // 2^32 expanded terms, but only about 1 MiB of indices and tokens.
    let raw = raw.build();
    let bytes = id_bytes(&f, &raw);
    assert!(bytes.len() < 1_060_000);
    assert_eq!(
        compute_id(&f, &raw),
        <[u8; 32]>::from(Sha256::digest(bytes))
    );
}

#[test]
fn coordinate_deltas_use_signed_64_bit_values() {
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let mut raw = fixture(&f).into_builder();
    let t = &mut raw.layers[0].quadratic.deltas[1];
    t.g = (-1i32) as u32;
    t.l = (-2i32) as u32;
    t.r = (-3i32) as u32;
    let mut expected = reference(&f);
    let record = b"LFC3-v2-segmented-id-v2".len()
        + 2 * 8
        + f.serialized_size_bytes()
        + 6 * 8
        + 2 * f.serialized_size_bytes()
        + 2 * 8
        + 5 * 8
        + 4 * 8;
    for (i, n) in [-1i64, -2, -3].into_iter().enumerate() {
        expected[record + i * 8..record + (i + 1) * 8].copy_from_slice(&n.to_le_bytes());
    }
    assert_eq!(id_bytes(&f, &raw.build()), expected);
}

#[test]
fn old_identity_revision_is_rejected() {
    use crate::core::proto::{
        v2::{Circuit, CircuitReader, CircuitWriter},
        FieldID,
    };
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let c = Circuit::from_raw(&f, fixture(&f));
    let mut bytes = CircuitWriter::new(&f, FieldID::Gf2_128).to_bytes(&c);
    let reader = CircuitReader::new(&f, FieldID::Gf2_128);
    assert!(reader.from_bytes(&bytes).is_ok());
    for revision in [b"DIR1", b"DIR2"] {
        bytes[4..8].copy_from_slice(revision);
        let error = reader
            .from_bytes(&bytes)
            .err()
            .expect("accepted an old identity revision");
        assert!(error.contains("DIR3"));
    }
}
