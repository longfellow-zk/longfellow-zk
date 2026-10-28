// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Inspect authenticated v9/ML-DSA archives; link against longfellow_zk.
use longfellow_zk::{
    core::{
        algebra::SerializableField,
        proto::{circuit::Circuit, reader::CircuitReader, FieldID},
    },
    mdoc::{development_provider as dev, v2::packed_v9},
    runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field, p256::P256Field, RuntimeField,
    },
};
fn show<const W: usize, F: SerializableField + RuntimeField<W>>(name: &str, c: &Circuit<F>, f: &F) {
    let counts = c.term_breakdown(f);
    let mut expanded = [[0usize; 3]; 3];
    for l in &c.raw.layers {
        for (d, s) in l.streams().enumerate() {
            s.for_each_term(&c.raw.constants, |t| {
                expanded[d][if f.is_zero(&t.k) {
                    0
                } else if t.k == f.one() {
                    1
                } else {
                    2
                }] += 1
            });
        }
    }
    assert_eq!(counts, expanded, "typed and expanded term counts differ");
    print!("{name}");
    for d in counts {
        for n in d {
            print!(",{n}");
        }
    }
    let slots = c.raw.layers.iter().map(|l| l.nw()).sum::<usize>();
    println!(
        ",{},{},{},{},{}",
        counts.iter().flatten().sum::<usize>(),
        slots,
        slots + c.raw.noutput - c.raw.ninput,
        c.raw.layers.len(),
        c.heap_bytes()
    );
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 2, "usage: inspect V9_CACHE MLDSA_ARCHIVES");
    println!("circuit,q_zero,q_one,q_other,l_zero,l_one,l_other,c_zero,c_one,c_other,total,layer_input_slots,wires,layers,current_decoder_heap_bytes");
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    for n in [2, 4] {
        let b = dev::read_packed_v9(std::path::Path::new(&format!(
            "{}/v9-uniform-inputs-{n}-0.cache",
            args[0]
        )))
        .unwrap();
        let (s, h) = packed_v9::provider::load(b.spec(), b.compressed(), &p, &f).unwrap();
        show(&format!("v9-hash-{n}"), &h, &f);
        if n == 2 {
            show("v9-signature", &s, &p);
        }
    }
    for n in [44, 65] {
        let f = RuntimeFp24Ext6::new();
        let raw = std::fs::read(format!("{}/MlDsa{n}.lfc2", args[1])).unwrap();
        let (c, tail) = CircuitReader::new(&f, FieldID::None)
            .from_bytes(&raw, true)
            .unwrap();
        assert!(tail.is_empty());
        show(&format!("ML-DSA-{n}"), &c, &f);
    }
}
