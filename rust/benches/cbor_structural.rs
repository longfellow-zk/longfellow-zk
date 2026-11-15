// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Scalar structural circuit geometry and offline synthesis time, not proof latency.
//! Every map and query shares one lexer and one complete-tree rank certificate.
use std::time::Instant;

use longfellow_zk::{
    circuits::bitvec::{BitvecIO, BitvecLogic},
    compile::{algebra::gf2_128::Gf2_128Field, compiler::compile_v2, logic::Logic},
    mdoc::{
        circuits::{
            cbor_lexer::{self, CborLexer},
            cbor_parser::{CborParser, RankWitness, Span, Witness},
        },
        proto::hash::constants::K_MSO_MAX_BYTES,
    },
};

fn main() {
    const N: usize = 12;
    let field = Gf2_128Field::new();
    println!("capacity,maps,queries_per_map,inputs,wires,terms,layers,synthesis_ms");
    for (capacity, maps, queries) in [
        (K_MSO_MAX_BYTES / 2, 1, 1),
        (K_MSO_MAX_BYTES, 0, 0),
        (K_MSO_MAX_BYTES, 1, 1),
        (K_MSO_MAX_BYTES, 1, 4),
        (K_MSO_MAX_BYTES, 2, 1),
        (K_MSO_MAX_BYTES, 4, 1),
    ] {
        let start = Instant::now();
        let (_, stats, _) = compile_v2(&field, |logic| {
            let bv = BitvecLogic::new(&logic);
            let io = BitvecIO::new(&bv);
            let mut pos = 1;
            let bytes: Vec<_> = (0..capacity).map(|_| io.next::<8>(&mut pos)).collect();
            let len = io.next::<N>(&mut pos);
            let lexical = cbor_lexer::Witness::<_, N>::allocate(&logic, capacity, &mut pos);
            let stream = CborLexer::new(&logic).lex(&bytes, &len, &lexical);
            if maps == 0 {
                return (stream.assertions(), 1);
            }
            let rank = RankWitness::<_, N>::allocate(&logic, capacity, &mut pos);
            let parser = CborParser::new(&logic);
            let parsed = parser.parse(stream, &rank);
            let witness = Witness::allocate(&logic, capacity, &mut pos);
            let mut map = parser.root_map(&parsed, &witness);
            let mut checks = Vec::new();
            for depth in 0..maps {
                for query in 0..queries {
                    let key = io.next::<N>(&mut pos);
                    let span = Span {
                        start: io.next::<N>(&mut pos),
                        end: io.next::<N>(&mut pos),
                    };
                    let entry = parser.entry(&map, &key, &span);
                    checks.push(entry.assertions());
                    if query + 1 == queries && depth + 1 < maps {
                        let nested = Witness::allocate(&logic, capacity, &mut pos);
                        map = parser.item_map(&entry.value, &nested);
                    }
                }
            }
            (logic.assert_all("entries", &checks), 1)
        });
        println!(
            "{capacity},{maps},{queries},{},{},{},{},{:.3}",
            stats.ninput,
            stats.nwires,
            stats.nterms,
            stats.nlayers,
            start.elapsed().as_secs_f64() * 1000.0
        );
    }
}
