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
    let mut b = b"LFC3-v2-segmented-id-v1".to_vec();
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
            0u8,
            [2u64, 2, 3, 1],
            vec![0u32, 1, 2, 0, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0],
        ),
        (1u8, [1u64, 1, 1, 1], vec![0u32, 3, 1, 1, 0, 0]),
        (2u8, [1u64, 1, 1, 1], vec![1u32, 0, 1, 0, 0]),
    ] {
        b.push(tag);
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
    // 2^32 expanded terms, but only about 512 KiB of indices and tokens.
    let raw = raw.build();
    let bytes = id_bytes(&f, &raw);
    assert!(bytes.len() < 530_000);
    assert_eq!(
        compute_id(&f, &raw),
        <[u8; 32]>::from(Sha256::digest(bytes))
    );
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
    bytes[4..8].copy_from_slice(b"DIR1");
    let error = reader
        .from_bytes(&bytes)
        .err()
        .expect("accepted an old identity revision");
    assert!(error.contains("DIR2"));
}
