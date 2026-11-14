// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    compile::{
        algebra::p256::P256Field,
        compiler::segment_circuit_v2,
        logic::{Logic, LogicIO},
    },
    core::proto::{
        v2::{CircuitReader, CircuitWriter, Stream},
        },
};
fn check_stream<T>(stream: &Stream<T>) {
    let mut deltas = vec![0; stream.deltas.len()];
    let mut segments = vec![0; stream.segments.len()];
    for &t in &stream.tokens {
        segments[t as usize] += 1;
        for &i in &stream.segments[t as usize] {
            deltas[i as usize] += 1;
        }
    }
    assert!(deltas.windows(2).all(|w| w[0] >= w[1]));
    assert!(segments.windows(2).all(|w| w[0] >= w[1]));
}
#[test]
fn circuit_compression_and_recompression_preserve_lfc3() {
    let f = P256Field::new();
    let (original, _, _) = super::compile(&f, |logic| {
        let mut x = logic.input(1);
        let y = logic.input(2);
        for _ in 0..40 {
            let sum = logic.add(&x, &y);
            x = logic.add(&logic.mul(&sum, &x), &y);
        }
        (logic.assert0("x", &x), 1, 0)
    });
    let original_id = original.id;
    let compressed = segment_circuit_v2(&f, original.into_raw());
    let compressed_id = compressed.id;
    let compressed_bytes = CircuitWriter::new(&f).to_bytes(&compressed);
    let recompressed = segment_circuit_v2(&f, compressed.into_raw());
    assert_eq!(original_id, compressed_id);
    assert_eq!(compressed_id, recompressed.id);
    let writer = CircuitWriter::new(&f);
    let bytes = compressed_bytes;
    assert_eq!(bytes, writer.to_bytes(&recompressed));
    let (decoded, tail) = CircuitReader::new(&f)
        .from_bytes(&bytes)
        .unwrap();
    assert!(tail.is_empty());
    assert_eq!(decoded.id, original_id);
    for l in &recompressed.raw.layers {
        check_stream(&l.quadratic);
        check_stream(&l.linear);
        check_stream(&l.constant);
    }
}
