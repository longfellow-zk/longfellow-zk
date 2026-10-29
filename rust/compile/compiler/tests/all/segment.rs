// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    compile::{
        algebra::p256::P256Field,
        compiler::segment_circuit_v2,
        logic::{Logic, LogicIO},
    },
    core::proto::{reader::CircuitReader, v2::Stream, writer::CircuitWriter, FieldID},
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
    let compressed = segment_circuit_v2(&f, &original);
    let recompressed = segment_circuit_v2(&f, &compressed);
    assert_eq!(original.id, compressed.id);
    assert_eq!(compressed.id, recompressed.id);
    let writer = CircuitWriter::new(&f, FieldID::P256);
    let bytes = writer.to_bytes_lfc3(&compressed);
    assert_eq!(bytes, writer.to_bytes_lfc3(&recompressed));
    let (decoded, tail) = CircuitReader::new(&f, FieldID::P256)
        .from_bytes_lfc3(&bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    assert_eq!(decoded.id, original.id);
    for l in &compressed.raw.layers {
        check_stream(&l.quadratic);
        check_stream(&l.quadratic_one);
        check_stream(&l.quadratic_minus_one);
        check_stream(&l.quadratic_assertions);
        check_stream(&l.linear);
        check_stream(&l.linear_one);
        check_stream(&l.linear_minus_one);
        check_stream(&l.linear_assertions);
        check_stream(&l.constant);
        check_stream(&l.constant_one);
        check_stream(&l.constant_minus_one);
    }
}
