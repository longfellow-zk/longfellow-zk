// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Check saved Morton streams using the actual no-sort round-major binder.
use core_proto::{FieldID, SerializableField};
use runtime_random::{RandomEngine, Transcript};

fn check<const W: usize, F>(f: &F, field: FieldID)
where
    F: runtime_algebra::SupportsSampling<W> + SerializableField,
{
    let bytes = std::fs::read(std::env::var("ORDER_PROOF_CIRCUIT").unwrap()).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let (c, tail) = reader.from_bytes(&bytes, true).unwrap();
    assert!(tail.is_empty());
    let mut transcript = Transcript::new(b"template-morton-fold-control");
    let mut nv = c.raw.noutput;
    let mut logv = c.raw.logv;
    for (index, layer) in c.raw.layers.iter().enumerate() {
        let g: Vec<_> = (0..logv)
            .map(|_| f.sample(|n| transcript.bytes(n)))
            .collect();
        let h: [Vec<_>; 2] = std::array::from_fn(|_| {
            (0..layer.logw())
                .map(|_| f.sample(|n| transcript.bytes(n)))
                .collect()
        });
        let beta = f.sample(|n| transcript.bytes(n));
        let dot = runtime_sumcheck::eq::eq2(logv, nv, &g, &g, &f.zero(), f);
        let eq0 = runtime_sumcheck::eq::eq2(layer.logw(), layer.nw(), &h[0], &h[0], &f.zero(), f);
        let eq1 = runtime_sumcheck::eq::eq2(layer.logw(), layer.nw(), &h[1], &h[1], &f.zero(), f);
        let mut expected = f.zero();
        layer.for_each_term(&c.raw.constants, |t| {
            let k = if f.is_zero(&t.k) { &beta } else { &t.k };
            let weight = f.mulf(
                &dot[t.g as usize],
                &f.mulf(&eq0[t.h0 as usize], &eq1[t.h1 as usize]),
            );
            f.add(&mut expected, &f.mulf(k, &weight));
        });
        let mut quad = runtime_sumcheck::HQuad::<W, F>::bind_g(
            layer,
            &c.raw.constants,
            logv,
            nv,
            &g,
            &g,
            &f.zero(),
            &beta,
            f,
        );
        for (hand, bit) in (0..2 * layer.logw()).map(|i| (i % 2, i / 2)) {
            quad.bind_h(&h[hand][bit], hand, f);
        }
        assert_eq!(
            quad.scalar(),
            expected,
            "Morton fold mismatch at layer {index}"
        );
        nv = layer.nw();
        logv = layer.logw();
    }
    println!(
        "MORTON_FOLDS layers={} verified=true runtime_sort=false",
        c.raw.layers.len()
    );
}

#[test]
#[ignore = "offline no-sort round-major compatibility check on saved circuits"]
fn stored_morton_folds() {
    match std::env::var("ORDER_DATASET").unwrap().as_str() {
        "mdoc_sig" => check::<4, _>(&runtime_algebra::p256::P256Field::new(), FieldID::P256),
        "mdoc_hash2" => check::<2, _>(
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            FieldID::Gf2_128,
        ),
        "mldsa44" | "mldsa65" => check::<3, _>(
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            FieldID::None,
        ),
        _ => panic!("unsupported Morton control dataset"),
    }
}
