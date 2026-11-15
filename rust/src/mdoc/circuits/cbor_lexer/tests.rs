// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CborLexer, Witness};
use crate::{
    circuits::{
        bitvec::{BitvecIO, BitvecLogic},
        boolean::Boolean,
    },
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, CompileField},
        compiler::{dump_stats, segment_circuit_v2},
        logic::{AssertionScope, EvalLogic},
    },
    core::proto::v2::evaluate::initial_inputs,
    mdoc::cbor::lexer_prover::ConcreteWitness,
    runtime::algebra::gf2_128::Gf2_128Field as RuntimeBinaryField,
};

fn evaluate<F: CompileField>(
    field: &F,
    bytes: &[u8],
    start: usize,
    end: usize,
    remaining: &[u64],
) -> (bool, Vec<bool>) {
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new_with_tracker(field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let b = Boolean::new(&logic);
    let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
    let stream = CborLexer::new(&logic).lex_range(
        &data,
        &bv.of_u64::<10>(start as u64),
        &bv.of_u64(end as u64),
        &Witness::constant(&logic, remaining),
    );
    let checks = stream.assertions();
    (
        checks.is_ok(),
        stream
            .headers()
            .iter()
            .map(|h| !field.is_zero(&b.as_eltw(h).value))
            .collect(),
    )
}

fn token_cases<F: CompileField>(field: &F) {
    // Every possible header, with sufficient argument/payload bytes. The
    // independent expected classification does not use the witness decoder.
    for header in 0u8..=255 {
        let mut bytes = vec![0; 64];
        bytes[0] = header;
        let major = header >> 5;
        let info = header & 31;
        let supported = info <= 27
            && (!matches!(major, 2..=5) || info <= 25)
            && (major != 7 || (20..=23).contains(&info));
        let width = match info {
            0..=23 => 1,
            24 => 2,
            25 => 3,
            26 => 5,
            _ => 9,
        };
        let end = width
            + if matches!(major, 2 | 3) && info < 24 {
                usize::from(info)
            } else {
                0
            };
        let remaining: Vec<_> = (0..bytes.len())
            .map(|i| if i < end { (end - i - 1) as u64 } else { 0 })
            .collect();
        assert_eq!(
            evaluate(field, &bytes, 0, end, &remaining).0,
            supported,
            "header {header:02x}"
        );
    }
}

#[test]
fn all_headers_in_binary_and_prime_fields() {
    token_cases(&Gf2_128Field::new());
    token_cases(&P256Field::new());
}

#[test]
fn actual_length_and_subranges_exclude_padding() {
    let field = Gf2_128Field::new();
    let mut bytes = vec![0xff; 64];
    bytes[7..13].copy_from_slice(&[0x43, 0xff, 0xa1, 0x61, 0x18, 0x01]);
    let witness = ConcreteWitness::derive_range(&bytes, 7, 13).unwrap();
    let (ok, headers) = evaluate(&field, &bytes, 7, 13, &witness.remaining);
    assert!(ok);
    assert_eq!(
        headers
            .iter()
            .enumerate()
            .filter_map(|(i, h)| h.then_some(i))
            .collect::<Vec<_>>(),
        [7, 11]
    );
    for end in [8, 9, 10, 12, 14, 65] {
        assert!(
            !evaluate(&field, &bytes, 7, end, &witness.remaining).0,
            "end {end}"
        );
    }
    assert!(evaluate(&field, &bytes, 7, 7, &vec![0; bytes.len()]).0);
    assert!(!evaluate(&field, &bytes, 8, 7, &witness.remaining).0);
}

#[test]
fn two_byte_lengths_and_truncated_headers() {
    let field = Gf2_128Field::new();
    let mut bytes = vec![0xff; 320];
    bytes[..3].copy_from_slice(&[0x59, 0x01, 0x00]);
    let witness = ConcreteWitness::derive(&bytes, 259).unwrap();
    assert!(evaluate(&field, &bytes, 0, 259, &witness.remaining).0);
    for end in [1, 2, 258] {
        assert!(!evaluate(&field, &bytes, 0, end, &witness.remaining).0);
    }
    for (index, byte) in [(1, 0x80), (2, 0xff)] {
        let mut corrupt = bytes.clone();
        corrupt[index] = byte;
        assert!(!evaluate(&field, &corrupt, 0, 259, &witness.remaining).0);
    }
}

#[test]
fn container_count_limits_distinguish_maps_from_arrays() {
    fn cases<F: CompileField>(field: &F) {
        for capacity in [16, 63, 64] {
            for count in [7u16, 8, 9, 16, 17, 31, 32, 33, 63, 64, 65, 255, 256, 65535] {
                for major in [4u8, 5] {
                    // The lexer checks the header's arity bound; tree
                    // completeness belongs to the parser, not this test.
                    let mut bytes = vec![0xff; capacity];
                    bytes[..3].copy_from_slice(&[
                        (major << 5) | 25,
                        (count >> 8) as u8,
                        count as u8,
                    ]);
                    let mut remaining = vec![0; capacity];
                    remaining[..2].copy_from_slice(&[2, 1]);
                    let limit = if major == 5 { capacity / 2 } else { capacity };
                    assert_eq!(
                        evaluate(field, &bytes, 0, 3, &remaining).0,
                        usize::from(count) <= limit,
                        "capacity {capacity}, major {major}, count {count}"
                    );
                }
            }
        }
    }
    cases(&Gf2_128Field::new());
    cases(&P256Field::new());
}

#[test]
fn every_countdown_witness_bit_is_checked() {
    let field = Gf2_128Field::new();
    let mut bytes = vec![0xff; 16];
    bytes[..7].copy_from_slice(&[0x43, 0xff, 0xa1, 0x61, 0x19, 0x01, 0x00]);
    let witness = ConcreteWitness::derive(&bytes, 7).unwrap();
    for i in 0..bytes.len() {
        for bit in 0..10 {
            let mut bad = witness.remaining.clone();
            bad[i] ^= 1 << bit;
            assert!(
                !evaluate(&field, &bytes, 0, 7, &bad).0,
                "remaining[{i}] bit {bit}"
            );
        }
    }
}

#[test]
fn compiled_lexer_accepts_runtime_lengths_and_rejects_truncation() {
    use crate::{
        compile::{compiler::compile_v2, debug::evaluate::eval_circuit_fc},
        core::algebra::AlgebraicField,
    };
    let fc = Gf2_128Field::new();
    let fr = RuntimeBinaryField::new();
    const CAP: usize = 32;
    const N: usize = 6;
    let (raw, stats, symbols) = compile_v2(&fc, |logic| {
        let bv = BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bv);
        let mut pos = 1;
        let bytes: Vec<_> = (0..CAP).map(|_| io.next::<8>(&mut pos)).collect();
        let len = io.next::<N>(&mut pos);
        let witness = Witness::<_, N>::allocate(&logic, CAP, &mut pos);
        (
            CborLexer::new(&logic)
                .lex(&bytes, &len, &witness)
                .assertions(),
            1,
        )
    });
    let circuit = segment_circuit_v2(&fc, raw);
    dump_stats("cbor_lexer_32", &circuit, &stats);
    for (payload, len, expected) in [
        (vec![0x41, 0xff], 2, true),
        (vec![0x41, 0xff], 1, false),
        (vec![0x18, 0x01], 2, true),
        (vec![0x18, 0x01], 1, false),
        (vec![], 0, true),
        (vec![0x1f], 1, false),
        (vec![0; CAP], CAP, true),
        (vec![0; CAP], CAP + 1, false),
    ] {
        let mut bytes = vec![0xff; CAP];
        bytes[..payload.len()].copy_from_slice(&payload);
        let witness = ConcreteWitness::derive(&bytes, payload.len()).unwrap_or(ConcreteWitness {
            remaining: vec![0; CAP],
            range: 0..payload.len(),
            headers: vec![false; CAP],
            arities: vec![0; CAP],
            maps: vec![false; CAP],
        });
        let mut inputs = initial_inputs(&fr);
        for byte in &bytes {
            for bit in 0..8 {
                inputs.push(if byte >> bit & 1 == 1 {
                    fr.one()
                } else {
                    fr.zero()
                });
            }
        }
        for (value, nbits) in
            std::iter::once((len as u64, N)).chain(witness.remaining.iter().map(|n| (*n, N)))
        {
            for bit in 0..nbits {
                inputs.push(if value >> bit & 1 == 1 {
                    fr.one()
                } else {
                    fr.zero()
                });
            }
        }
        let result = eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs).unwrap();
        assert_eq!(result.failed_paths().is_empty(), expected, "length {len}");
    }
}
