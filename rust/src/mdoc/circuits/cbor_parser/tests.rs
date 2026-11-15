// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CborParser, RankWitness, Span, Witness};
use crate::{
    circuits::bitvec::BitvecLogic,
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, CompileField},
        compiler::{dump_stats, segment_circuit_v2},
        logic::{AssertionScope, EvalLogic, Logic},
    },
    core::{
        algebra::{FieldID, SerializableField},
        proto::v2::evaluate::initial_inputs,
    },
    mdoc::{
        cbor::{
            lexer_prover,
            parse::CborElement,
            parser_prover::{ConcreteRankWitness as ConcreteRank, ConcreteWitness},
        },
        circuits::cbor_lexer::{self, CborLexer},
        proto::hash::constants::{K_MSO_MAX_BYTES, K_MSO_OFFSET},
        testcases::TEST_DATA,
    },
    runtime::algebra::{
        gf2_128::Gf2_128Field as RuntimeBinaryField, p256::P256Field as RuntimePrimeField,
        RuntimeField,
    },
};

fn check<F: CompileField>(
    field: &F,
    bytes: &[u8],
    len: usize,
    rank: &[u64],
    threshold: &[u64],
    query: Option<(usize, usize, usize)>,
) -> bool {
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new_with_tracker(field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let lex_witness = lexer_prover::ConcreteWitness::derive(bytes, len).unwrap();
    let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
    let stream = CborLexer::new(&logic).lex(
        &data,
        &bv.of_u64::<10>(len as u64),
        &cbor_lexer::Witness::constant(&logic, &lex_witness.remaining),
    );
    let parser = CborParser::new(&logic);
    let parsed = parser.parse(stream, &RankWitness::constant(&logic, rank));
    let map = parser.root_map(&parsed, &Witness::constant(&logic, threshold));
    match query {
        None => map.assertions().is_ok(),
        Some((k, v, e)) => parser
            .entry(
                &map,
                &bv.of_u64(k as u64),
                &Span {
                    start: bv.of_u64(v as u64),
                    end: bv.of_u64(e as u64),
                },
            )
            .assertions()
            .is_ok(),
    }
}

fn padded(hex: &str) -> (Vec<u8>, usize) {
    let mut bytes = hex::decode(hex).unwrap();
    let len = bytes.len();
    bytes.resize(32.max(len), 0xff);
    (bytes, len)
}

fn cases<F: CompileField>(field: &F) {
    for (hex, valid, invalid) in [
        (
            "a26161016162820102",
            vec![(1, 3, 4), (4, 6, 9)],
            vec![(2, 3, 4), (1, 6, 9), (3, 4, 6), (4, 6, 8), (1, 3, 9)],
        ),
        (
            "a16178a1616101",
            vec![(1, 3, 7)],
            vec![(4, 6, 7), (1, 3, 6)],
        ),
        (
            "a1616145616101a0ff",
            vec![(1, 3, 9)],
            vec![(4, 6, 7), (1, 3, 8)],
        ),
        // Container keys, empty containers, and tags are complete items too.
        ("a1810102", vec![(1, 3, 4)], vec![(2, 3, 4)]),
        (
            "a2a080c00181a0",
            vec![(1, 2, 3), (3, 5, 7)],
            vec![(4, 5, 7)],
        ),
    ] {
        let (bytes, len) = padded(hex);
        let lexical = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
        let rank = ConcreteRank::derive(&lexical).unwrap();
        let w = ConcreteWitness::derive(&lexical, &rank, 0, len).unwrap();
        assert!(
            check(field, &bytes, len, &rank.rank, &w.threshold, None),
            "{hex}"
        );
        for q in valid {
            assert!(
                check(field, &bytes, len, &rank.rank, &w.threshold, Some(q)),
                "{hex} {q:?}"
            );
        }
        for q in invalid {
            assert!(
                !check(field, &bytes, len, &rank.rank, &w.threshold, Some(q)),
                "{hex} {q:?}"
            );
        }
    }
}

#[test]
fn direct_entries_in_gf128() {
    cases(&Gf2_128Field::new());
}

#[test]
fn direct_entries_in_prime_field() {
    cases(&P256Field::new());
}

#[test]
fn witness_map_end_must_stay_in_the_lexed_range() {
    let bytes = [0xa0, 0x00, 0xa0];
    let lexical = lexer_prover::ConcreteWitness::derive(&bytes, 1).unwrap();
    let rank = ConcreteRank::derive(&lexical).unwrap();
    assert!(ConcreteWitness::derive(&lexical, &rank, 0, 1).is_ok());
    assert!(ConcreteWitness::derive(&lexical, &rank, 0, 2).is_err());
    assert!(ConcreteWitness::derive(&lexical, &rank, 0, 3).is_err());
    let subrange_lexical = lexer_prover::ConcreteWitness::derive_range(&bytes, 2, 3).unwrap();
    let subrange_rank = ConcreteRank::derive(&subrange_lexical).unwrap();
    assert!(ConcreteWitness::derive(&subrange_lexical, &subrange_rank, 2, 3).is_ok());
    assert!(ConcreteWitness::derive(&subrange_lexical, &subrange_rank, 0, 1).is_err());
}

fn exhaustive_offsets<F: CompileField>(field: &F) {
    use crate::mdoc::cbor::parse::{CborParser as HostParser, CborValue};
    for hex in ["a16161820102", "a2a0006162a1616301", "a1616145616101a0ff"] {
        let bytes = hex::decode(hex).unwrap();
        let host = HostParser::new(&bytes).parse_exact().unwrap();
        let CborValue::Map(entries) = host.value else {
            unreachable!()
        };
        let expected: Vec<_> = entries
            .iter()
            .map(|(k, v)| (k.start, v.start, v.end))
            .collect();
        let lexical = lexer_prover::ConcreteWitness::derive(&bytes, bytes.len()).unwrap();
        let rank = ConcreteRank::derive(&lexical).unwrap();
        let witness = ConcreteWitness::derive(&lexical, &rank, 0, bytes.len()).unwrap();
        let tracker = AssertionScope::new();
        let logic = EvalLogic::new(field, &tracker);
        let bv = BitvecLogic::new(&logic);
        let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
        let stream = CborLexer::new(&logic).lex(
            &data,
            &bv.of_u64::<6>(bytes.len() as u64),
            &cbor_lexer::Witness::constant(&logic, &lexical.remaining),
        );
        let parser = CborParser::new(&logic);
        let parsed = parser.parse(stream, &RankWitness::constant(&logic, &rank.rank));
        let map = parser.root_map(&parsed, &Witness::constant(&logic, &witness.threshold));
        let offsets: Vec<_> = (0..=bytes.len() + 1).chain(std::iter::once(63)).collect();
        for &k in &offsets {
            for &v in &offsets {
                for &end in &offsets {
                    let result = parser
                        .entry(
                            &map,
                            &bv.of_u64(k as u64),
                            &Span {
                                start: bv.of_u64(v as u64),
                                end: bv.of_u64(end as u64),
                            },
                        )
                        .assertions();
                    assert_eq!(
                        result.is_ok(),
                        expected.contains(&(k, v, end)),
                        "{hex}: {k}, {v}, {end}"
                    );
                }
            }
        }
    }
}

#[test]
fn every_offset_combination_agrees_with_the_host_parser() {
    exhaustive_offsets(&Gf2_128Field::new());
}

#[test]
fn malformed_containers_are_not_just_lexical_errors() {
    let field = Gf2_128Field::new();
    for hex in [
        "a16161",
        "a0616101",
        "a161618201",
        "a16161c0",
        "a161610100",
        "a1616142a00100",
        "816161",
    ] {
        let (bytes, len) = padded(hex);
        let zero = vec![0; bytes.len()];
        assert!(!check(&field, &bytes, len, &zero, &zero, None), "{hex}");
    }
    let (bytes, len) = padded("a0");
    assert!(check(
        &field,
        &bytes,
        len,
        &vec![0; bytes.len()],
        &vec![0; bytes.len()],
        None
    ));
}

#[test]
fn every_parser_witness_bit_is_checked() {
    let field = Gf2_128Field::new();
    let (bytes, len) = padded("a26161016162820102");
    let lexical = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
    let rank = ConcreteRank::derive(&lexical).unwrap();
    let w = ConcreteWitness::derive(&lexical, &rank, 0, len).unwrap();
    for state in 0..2 {
        for i in 0..bytes.len() {
            for bit in 0..10 {
                let mut bad_rank = rank.clone();
                let mut bad = w.clone();
                if state == 0 {
                    bad_rank.rank[i] ^= 1 << bit;
                } else {
                    bad.threshold[i] ^= 1 << bit;
                }
                assert!(
                    !check(&field, &bytes, len, &bad_rank.rank, &bad.threshold, None),
                    "state {state} byte {i} bit {bit}"
                );
            }
        }
    }
}

#[test]
fn nested_map_handles_retain_ancestry() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new_with_tracker(&field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let (bytes, len) = padded("a16178a1616101");
    let lexical = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
    let rank = ConcreteRank::derive(&lexical).unwrap();
    let w = ConcreteWitness::derive(&lexical, &rank, 0, len).unwrap();
    let nested_w = ConcreteWitness::derive(&lexical, &rank, 3, 7).unwrap();
    let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
    let stream = CborLexer::new(&logic).lex(
        &data,
        &bv.of_u64::<10>(len as u64),
        &cbor_lexer::Witness::constant(&logic, &lexical.remaining),
    );
    let parser = CborParser::new(&logic);
    let parsed = parser.parse(stream, &RankWitness::constant(&logic, &rank.rank));
    let root = parser.root_map(&parsed, &Witness::constant(&logic, &w.threshold));
    let outer = parser.entry(
        &root,
        &bv.of_u64(1),
        &Span {
            start: bv.of_u64(3),
            end: bv.of_u64(7),
        },
    );
    let nested = parser.item_map(
        &outer.value,
        &Witness::constant(&logic, &nested_w.threshold),
    );
    assert!(parser
        .entry(
            &nested,
            &bv.of_u64(4),
            &Span {
                start: bv.of_u64(6),
                end: bv.of_u64(7)
            }
        )
        .assertions()
        .is_ok());
    // Lexical checks must survive all the way through a nested entry.
    let mut bad_lexical = lexical.remaining.clone();
    bad_lexical[2] = 1;
    let bad_stream = CborLexer::new(&logic).lex(
        &data,
        &bv.of_u64::<10>(len as u64),
        &cbor_lexer::Witness::constant(&logic, &bad_lexical),
    );
    let bad_parsed = parser.parse(bad_stream, &RankWitness::constant(&logic, &rank.rank));
    let bad_root = parser.root_map(&bad_parsed, &Witness::constant(&logic, &w.threshold));
    let bad_outer = parser.entry(
        &bad_root,
        &bv.of_u64(1),
        &Span {
            start: bv.of_u64(3),
            end: bv.of_u64(7),
        },
    );
    let bad_nested = parser.item_map(
        &bad_outer.value,
        &Witness::constant(&logic, &nested_w.threshold),
    );
    assert!(parser
        .entry(
            &bad_nested,
            &bv.of_u64(4),
            &Span {
                start: bv.of_u64(6),
                end: bv.of_u64(7)
            }
        )
        .assertions()
        .is_err());
}

fn compiled_cases<FC, FR>(fc: &FC, fr: &FR, field_id: FieldID)
where
    FC: CompileField,
    FR: RuntimeField + SerializableField,
{
    use crate::{
        circuits::bitvec::BitvecIO,
        compile::{compiler::compile_v2, debug::evaluate::eval_circuit_fc},
    };
    const CAP: usize = 16;
    const N: usize = 5;
    let (raw, stats, symbols) = compile_v2(fc, |logic| {
        let bv = BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bv);
        let mut pos = 1;
        let bytes: Vec<_> = (0..CAP).map(|_| io.next::<8>(&mut pos)).collect();
        let len = io.next::<N>(&mut pos);
        let lex_witness = cbor_lexer::Witness::<_, N>::allocate(&logic, CAP, &mut pos);
        let rank = RankWitness::<_, N>::allocate(&logic, CAP, &mut pos);
        let witness = Witness::<_, N>::allocate(&logic, CAP, &mut pos);
        let key = io.next::<N>(&mut pos);
        let value = Span {
            start: io.next::<N>(&mut pos),
            end: io.next::<N>(&mut pos),
        };
        let stream = CborLexer::new(&logic).lex(&bytes, &len, &lex_witness);
        let parser = CborParser::new(&logic);
        let parsed = parser.parse(stream, &rank);
        let root = parser.root_map(&parsed, &witness);
        (parser.entry(&root, &key, &value).assertions(), 1)
    });
    let circuit = segment_circuit_v2(fc, raw);
    dump_stats(&format!("cbor_map_entry_16_{field_id:?}"), &circuit, &stats);
    let mut bytes = hex::decode("a26161016162820102").unwrap();
    let len = bytes.len();
    bytes.resize(CAP, 0xff);
    let lex = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
    let rank = ConcreteRank::derive(&lex).unwrap();
    let parsed = ConcreteWitness::derive(&lex, &rank, 0, len).unwrap();
    let evaluate = |key: usize, value: usize, end: usize, actual: usize, bad: Option<usize>| {
        let mut input = initial_inputs(fr);
        let mut push = |word: u64, width: usize| {
            for bit in 0..width {
                input.push(if word >> bit & 1 == 1 {
                    fr.one()
                } else {
                    fr.zero()
                });
            }
        };
        for byte in &bytes {
            push(u64::from(*byte), 8);
        }
        push(actual as u64, N);
        for count in &lex.remaining {
            push(*count, N);
        }
        for i in 0..CAP {
            push(rank.rank[i] ^ u64::from(bad == Some(i)), N);
        }
        for n in &parsed.threshold {
            push(*n, N);
        }
        for offset in [key, value, end] {
            push(offset as u64, N);
        }
        eval_circuit_fc(fc, fr, &circuit, &symbols, &input)
            .unwrap()
            .failed_paths()
            .is_empty()
    };
    assert!(evaluate(1, 3, 4, len, None));
    assert!(evaluate(4, 6, 9, len, None));
    for (k, v, e) in [
        (2, 3, 4),
        (1, 6, 9),
        (3, 4, 6),
        (4, 6, 8),
        (1, 3, 9),
        (1, 3, 31),
    ] {
        assert!(!evaluate(k, v, e, len, None), "{k} {v} {e}");
    }
    for actual in [0, 4, len - 1, len + 1, CAP + 1] {
        assert!(!evaluate(1, 3, 4, actual, None));
    }
    for i in 0..CAP {
        assert!(!evaluate(1, 3, 4, len, Some(i)));
    }
}

#[test]
fn compiled_membership_and_runtime_length_in_gf128() {
    use crate::core::algebra::FieldID;
    compiled_cases(
        &Gf2_128Field::new(),
        &RuntimeBinaryField::new(),
        FieldID::Gf2_128,
    );
}

#[test]
fn compiled_membership_and_runtime_length_in_prime_field() {
    use crate::core::algebra::FieldID;
    compiled_cases(&P256Field::new(), &RuntimePrimeField::new(), FieldID::P256);
}

#[test]
fn mdoc_mso_entries_agree_with_the_host_parser() {
    use crate::{
        compile::algebra::CompileNat,
        mdoc::cbor::{
            parse::{CborParser as HostParser, CborValue},
            test_utils::parse_test_data,
        },
    };
    let (_, mdoc, _) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let mut bytes = mdoc.cbor_mso[K_MSO_OFFSET..].to_vec();
    let len = bytes.len();
    let host = HostParser::new(&bytes).parse_exact().unwrap();
    let CborValue::Map(entries) = host.value else {
        panic!("MSO root map");
    };
    bytes.resize(bytes.len().next_power_of_two(), 0xff);
    let lexical = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
    let rank = ConcreteRank::derive(&lexical).unwrap();
    let witness = ConcreteWitness::derive(&lexical, &rank, 0, len).unwrap();
    let field = Gf2_128Field::new();
    // One circuit scan serves all root entry queries.
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new_with_tracker(&field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
    let stream = CborLexer::new(&logic).lex(
        &data,
        &bv.of_u64::<12>(len as u64),
        &cbor_lexer::Witness::constant(&logic, &lexical.remaining),
    );
    let parser = CborParser::new(&logic);
    let parsed = parser.parse(stream, &RankWitness::constant(&logic, &rank.rank));
    let root = parser.root_map(&parsed, &Witness::constant(&logic, &witness.threshold));
    for (key, value) in entries {
        parser
            .entry(
                &root,
                &bv.of_u64(key.start as u64),
                &Span {
                    start: bv.of_u64(value.start as u64),
                    end: bv.of_u64(value.end as u64),
                },
            )
            .assertions()
            .assert_all_passed();
    }
}

#[test]
fn target_mso_capacity_circuit_size() {
    use crate::{circuits::bitvec::BitvecIO, compile::compiler::compile_v2};
    const N: usize = 12;
    const CAPACITY: usize = K_MSO_MAX_BYTES;
    let field = Gf2_128Field::new();
    let mut terms = Vec::new();
    let mut half_terms = 0;
    for (capacity, queries) in [
        (CAPACITY / 2, 1),
        (CAPACITY, 0),
        (CAPACITY, 1),
        (CAPACITY, 2),
    ] {
        let (circuit, stats, _) = compile_v2(&field, |logic| {
            let bv = BitvecLogic::new(&logic);
            let io = BitvecIO::new(&bv);
            let mut pos = 1;
            let bytes: Vec<_> = (0..capacity).map(|_| io.next::<8>(&mut pos)).collect();
            let len = io.next::<N>(&mut pos);
            let lex_witness = cbor_lexer::Witness::<_, N>::allocate(&logic, capacity, &mut pos);
            let stream = CborLexer::new(&logic).lex(&bytes, &len, &lex_witness);
            if queries == 0 {
                return (stream.assertions(), 1);
            }
            let rank = RankWitness::<_, N>::allocate(&logic, capacity, &mut pos);
            let witness = Witness::<_, N>::allocate(&logic, capacity, &mut pos);
            let parser = CborParser::new(&logic);
            let parsed = parser.parse(stream, &rank);
            let root = parser.root_map(&parsed, &witness);
            let checks: Vec<_> = (0..queries)
                .map(|_| {
                    let key = io.next::<N>(&mut pos);
                    let value = Span {
                        start: io.next::<N>(&mut pos),
                        end: io.next::<N>(&mut pos),
                    };
                    parser.entry(&root, &key, &value).assertions()
                })
                .collect();
            (Logic::assert_all(&logic, "entries", &checks), 1)
        });
        dump_stats(
            &format!("cbor_{capacity}_queries_{queries}"),
            &circuit,
            &stats,
        );
        assert!(
            stats.nterms < capacity * [476, 724, 736][queries],
            "structural circuit size regression"
        );
        assert!(
            stats.nlayers <= 16,
            "scan depth must not grow with byte count"
        );
        if capacity == CAPACITY / 2 {
            half_terms = stats.nterms;
        } else {
            terms.push(stats.nterms);
        }
    }
    assert!(
        terms[2] - terms[1] < terms[1] - terms[0],
        "additional queries should reuse the map scan"
    );
    assert!(
        terms[1] < 23 * half_terms / 10,
        "capacity cost must stay approximately linear"
    );
}

#[test]
fn nested_key_and_value_maps_share_rank_with_relative_parity() {
    use crate::mdoc::cbor::parse::{CborParser as HostParser, CborValue};
    // Maps used as keys have odd end-rank baselines. Value maps have even ones.
    // All four map scans below must reuse the same complete-tree certificate.
    let bytes = hex::decode("a2a10102a10304a1050607").unwrap();
    let host = HostParser::new(&bytes).parse_exact().unwrap();
    let lex = lexer_prover::ConcreteWitness::derive(&bytes, bytes.len()).unwrap();
    let rank = ConcreteRank::derive(&lex).unwrap();
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(&field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
    let stream = CborLexer::new(&logic).lex(
        &data,
        &bv.of_u64::<6>(bytes.len() as u64),
        &cbor_lexer::Witness::constant(&logic, &lex.remaining),
    );
    let parser = CborParser::new(&logic);
    let parsed = parser.parse(stream, &RankWitness::constant(&logic, &rank.rank));
    let root_w = ConcreteWitness::derive(&lex, &rank, 0, bytes.len()).unwrap();
    let root = parser.root_map(&parsed, &Witness::constant(&logic, &root_w.threshold));
    let mut todo = vec![(root, &host)];
    let mut maps = 0;
    while let Some((map, host_map)) = todo.pop() {
        maps += 1;
        let CborValue::Map(entries) = &host_map.value else {
            unreachable!()
        };
        let expected: Vec<_> = entries
            .iter()
            .map(|(k, v)| (k.start, v.start, v.end))
            .collect();
        for k in 0..=bytes.len() + 1 {
            for v in 0..=bytes.len() + 1 {
                for end in 0..=bytes.len() + 1 {
                    let entry = parser.entry(
                        &map,
                        &bv.of_u64(k as u64),
                        &Span {
                            start: bv.of_u64(v as u64),
                            end: bv.of_u64(end as u64),
                        },
                    );
                    assert_eq!(
                        entry.assertions().is_ok(),
                        expected.contains(&(k, v, end)),
                        "map {}..{}: {k} {v} {end}",
                        host_map.start,
                        host_map.end
                    );
                }
            }
        }
        for (k, v) in entries {
            let entry = parser.entry(
                &map,
                &bv.of_u64(k.start as u64),
                &Span {
                    start: bv.of_u64(v.start as u64),
                    end: bv.of_u64(v.end as u64),
                },
            );
            for (item, child) in [(&entry.key, k), (&entry.value, v)] {
                if matches!(child.value, CborValue::Map(_)) {
                    let w = ConcreteWitness::derive(&lex, &rank, child.start, child.end).unwrap();
                    todo.push((
                        parser.item_map(item, &Witness::constant(&logic, &w.threshold)),
                        child,
                    ));
                }
            }
        }
    }
    assert_eq!(maps, 4);
}

#[test]
fn global_rank_cannot_restart_after_a_complete_root() {
    let field = Gf2_128Field::new();
    for hex in ["a0c0", "a0a100"] {
        let (bytes, len) = padded(hex);
        let lex = lexer_prover::ConcreteWitness::derive(&bytes, len).unwrap();
        assert!(ConcreteRank::derive(&lex).is_err());
        // These satisfy the net rank equations and end at zero, but start a
        // second, incomplete tree after the first root has already completed.
        let mut pending = 1;
        let rank: Vec<_> = lex
            .headers
            .iter()
            .enumerate()
            .map(|(i, h)| {
                if *h {
                    pending = pending + lex.arities[i] - 1;
                }
                pending
            })
            .collect();
        assert_eq!(pending, 0);
        assert!(!check(
            &field,
            &bytes,
            len,
            &rank,
            &vec![0; bytes.len()],
            None
        ));
    }
}

fn nested_subrange_entries<F: CompileField>(field: &F) {
    use crate::mdoc::cbor::parse::{CborParser as HostParser, CborValue};
    for hex in [
        "a300a20102030401a005a106a0",
        "a28101a100c001a0a10102",
        "a26161c0a1616201616382a1616402a0",
        // Non-minimal but supported 16-bit container counts.
        "b9000100b900010001",
    ] {
        // Deliberately place fake maps in both unlexed prefix and padding.
        let mut bytes = hex::decode("a100a0").unwrap();
        let start = bytes.len();
        bytes.extend(hex::decode(hex).unwrap());
        let end = bytes.len();
        bytes.extend_from_slice(&[0xa1, 0, 0xa0]);
        let mut host = HostParser::new(&bytes[start..end]).parse_exact().unwrap();
        // Host offsets are relative to the sliced input.
        fn relocate(item: &mut CborElement, base: usize) {
            item.start += base;
            item.end += base;
            match &mut item.value {
                CborValue::Map(entries) => {
                    for (k, v) in entries {
                        relocate(k, base);
                        relocate(v, base);
                    }
                }
                CborValue::Array(items) => {
                    for child in items {
                        relocate(child, base);
                    }
                }
                CborValue::Tag(_, child) => relocate(child, base),
                _ => {}
            }
        }
        relocate(&mut host, start);
        let lex = lexer_prover::ConcreteWitness::derive_range(&bytes, start, end).unwrap();
        let rank = ConcreteRank::derive(&lex).unwrap();
        let tracker = AssertionScope::new();
        let logic = EvalLogic::new(field, &tracker);
        let bv = BitvecLogic::new(&logic);
        let data: Vec<_> = bytes.iter().map(|v| bv.of_u8(*v)).collect();
        let stream = CborLexer::new(&logic).lex_range(
            &data,
            &bv.of_u64::<6>(start as u64),
            &bv.of_u64(end as u64),
            &cbor_lexer::Witness::constant(&logic, &lex.remaining),
        );
        let parser = CborParser::new(&logic);
        let parsed = parser.parse(stream, &RankWitness::constant(&logic, &rank.rank));
        let w = ConcreteWitness::derive(&lex, &rank, start, end).unwrap();
        let root = parser.root_map(&parsed, &Witness::constant(&logic, &w.threshold));
        let mut todo = vec![(root, &host)];
        while let Some((map, item)) = todo.pop() {
            map.assertions().assert_all_passed();
            let CborValue::Map(entries) = &item.value else {
                unreachable!()
            };
            let expected: Vec<_> = entries
                .iter()
                .map(|(k, v)| (k.start, v.start, v.end))
                .collect();
            for (k, v) in entries {
                // Move each endpoint across headers, payload, sibling maps,
                // unlexed bytes and out-of-capacity offsets independently.
                for offset in (0..=bytes.len()).chain(std::iter::once(63)) {
                    for query in [
                        (offset, v.start, v.end),
                        (k.start, offset, v.end),
                        (k.start, v.start, offset),
                    ] {
                        let result = parser.entry(
                            &map,
                            &bv.of_u64(query.0 as u64),
                            &Span {
                                start: bv.of_u64(query.1 as u64),
                                end: bv.of_u64(query.2 as u64),
                            },
                        );
                        assert_eq!(
                            result.assertions().is_ok(),
                            expected.contains(&query),
                            "{hex}: {query:?}"
                        );
                    }
                }
                let entry = parser.entry(
                    &map,
                    &bv.of_u64(k.start as u64),
                    &Span {
                        start: bv.of_u64(v.start as u64),
                        end: bv.of_u64(v.end as u64),
                    },
                );
                for (checked, child) in [(&entry.key, k), (&entry.value, v)] {
                    if matches!(child.value, CborValue::Map(_)) {
                        let child_w =
                            ConcreteWitness::derive(&lex, &rank, child.start, child.end).unwrap();
                        todo.push((
                            parser
                                .item_map(checked, &Witness::constant(&logic, &child_w.threshold)),
                            child,
                        ));
                    }
                }
            }
        }
    }
}

#[test]
fn nested_subranges_exclude_prefix_payload_and_sibling_maps() {
    nested_subrange_entries(&Gf2_128Field::new());
    nested_subrange_entries(&P256Field::new());
}
