// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Foreign storage unit tests: typed words, the fixed fragment and its leaves.
use super::{
    adapter::{fragment, virtual_inputs, Leaf, TreeInstance, TreeShape},
    word::{MaskedWord, Otp, Word},
};
use crate::{
    core::algebra::{AlgebraicField, SupportsU128Conversions},
    runtime::{algebra::gf2_128::Gf2_128Field, random::DeterministicRng},
};

#[test]
fn masked_word_codec_is_canonical() {
    let mut rng = DeterministicRng::new(7);
    let k = Word::<10>::new(0x2a5).unwrap();
    assert!(Word::<10>::new(1 << 10).is_err());
    let o = Otp::<10>::sample(&mut rng);
    let m = MaskedWord::mask(k, &o);
    let bytes = m.encoded();
    assert_eq!(bytes.len(), 2);
    let mut read = bytes.as_slice();
    assert_eq!(MaskedWord::<10>::read(&mut read).unwrap(), m);
    assert!(read.is_empty());
    // Any nonzero padding bit is rejected.
    for bit in 2..8 {
        let mut bad = bytes.clone();
        bad[1] |= 1 << bit;
        assert!(MaskedWord::<10>::read(&mut bad.as_slice()).is_err());
    }
    assert!(MaskedWord::<10>::read(&mut &bytes[..1]).is_err());
    // Unmasking recovers k bit by bit.
    let pad: Vec<_> = o.bits().collect();
    for (j, &p) in pad.iter().enumerate() {
        assert_eq!(m.bit(j) ^ p, (k.value() >> j) & 1 != 0);
    }
}

#[test]
fn fragment_accepts_exactly_unit_products() {
    use crate::runtime::v2::sumcheck;
    let f = Gf2_128Field::new();
    for leaves in [2, 3, 5, 8, 13] {
        let shape = TreeShape { trees: 2, leaves };
        let (npublic, start) = (3, 11);
        let c = fragment(npublic, start, shape).unwrap();
        assert_eq!(c.raw.ninput, start + 2 * leaves);
        assert_eq!(c.raw.noutput, 2);
        // Committed bits: 0/1 values at [npublic, start).
        let bits: Vec<_> = (0..start)
            .map(|i| f.u128_to_element((i % 2) as u128))
            .collect();
        let x = f.u128_to_element(7);
        let trees = (0..2)
            .map(|t| {
                let leaves: Vec<_> = (0..leaves)
                    .map(|i| Leaf::data(npublic + (i + t) % (start - npublic), x, &f))
                    .collect();
                // Honest target: the product of the leaf values.
                let target = leaves.iter().fold(f.one(), |acc, l| {
                    let v = f.addf(&l.constant, &f.mulf(&l.coefficient, &bits[l.source]));
                    f.mulf(&acc, &v)
                });
                TreeInstance { leaves, target }
            })
            .collect();
        let v = virtual_inputs(shape, trees, &f).unwrap();
        let mut inputs = bits.clone();
        for e in &v.entries {
            inputs.push(f.addf(&e.constant, &f.mulf(&e.coefficient, &bits[e.source])));
        }
        sumcheck::eval_circuit(inputs.clone(), &c, &f).unwrap();
        // Perturb one leaf: the product is no longer one.
        let mut bad = inputs.clone();
        bad[start] = f.addf(&bad[start], &f.one());
        assert!(sumcheck::eval_circuit(bad, &c, &f).is_err());
    }
}
