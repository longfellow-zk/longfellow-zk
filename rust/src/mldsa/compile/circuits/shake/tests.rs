// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    circuits::bitvec::BitvecIO,
    compile::{
        algebra::gf2_128::Gf2_128Field as CF,
        compiler::{compile_v2_shared_inputs, segment_circuit_v2},
    },
    core::proto::v2::{CircuitReader, CircuitWriter},
    runtime::{
        algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as RF},
        v2::sumcheck::eval_circuit,
    },
};
#[test]
fn scalar_and_simd_shake128_256_match_independent_xof_at_boundaries() {
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    for rate in [136, 168] {
        for len in [0, rate - 1, rate, rate + 1] {
            let message: Vec<_> = (0..len).map(|i| (i * 37) as u8).collect();
            let out_len = rate + 1;
            let mut expected = vec![0; out_len];
            if rate == 136 {
                let mut h = sha3::Shake256::default();
                h.update(&message);
                h.finalize_xof().read(&mut expected);
            } else {
                let mut h = sha3::Shake128::default();
                h.update(&message);
                h.finalize_xof().read(&mut expected);
            }
            for external in [false, true] {
                let k = BinaryKeccak {
                    external_permutations: external,
                    ..BinaryKeccak::default()
                };
                let cf = CF::new();
                let mut links = vec![];
                let (unsegmented, _, _) = compile_v2_shared_inputs(&cf, |l| {
                    let mut pos = 1;
                    let bv = BitvecLogic::new(&l);
                    let io = BitvecIO::new(&bv);
                    let output: Vec<_> = (0..out_len).map(|_| io.next::<8>(&mut pos)).collect();
                    let public = pos;
                    let input: Vec<_> = (0..len).map(|_| io.next::<8>(&mut pos)).collect();
                    let witness = allocate_witness_with_rate(&bv, &mut pos, len, out_len, k, rate);
                    links = witness.links(&l);
                    let gadget = if rate == 136 {
                        Shake256::with_keccak(&l, k)
                    } else {
                        Shake256::shake128(&l, k)
                    };
                    let (actual, valid) = gadget.assert_hash(&input, out_len, &witness);
                    let mut checks = vec![valid];
                    checks.extend(
                        actual
                            .iter()
                            .zip(output)
                            .map(|(a, b)| bv.assert_eq("digest", a, &b)),
                    );
                    let external_ranges = links
                        .iter()
                        .flat_map(|(a, b)| {
                            [a[0] + 1..a[a.len() - 1] + 2, b[0] + 1..b[b.len() - 1] + 2]
                        })
                        .collect();
                    (l.assert_all("SHAKE", &checks), public, external_ranges)
                });
                let compiled = segment_circuit_v2(&cf, unsegmented);
                let bytes = CircuitWriter::new(&cf).to_bytes(&compiled);
                let f = RF::new();
                let (c, tail) = CircuitReader::new(&f).from_bytes(&bytes).unwrap();
                assert!(tail.is_empty());
                let (output, trace) = if rate == 136 {
                    crate::mldsa::runtime::reference::shake256_witness(&message, out_len)
                } else {
                    crate::mldsa::runtime::reference::shake128_witness(&message, out_len)
                };
                assert_eq!(output, expected);
                let mut input: Vec<_> = expected
                    .iter()
                    .chain(&message)
                    .flat_map(|b| (0..8).map(move |r| E::from((b >> r & 1) as u128)))
                    .collect();
                trace.push_wires_with_keccak(&f, &mut input, k);
                assert_eq!(input.len(), c.raw.ninput);
                eval_circuit(input.clone(), &c, &f).unwrap();
                let mut bad = input.clone();
                bad[0].xor_in_place(&E::from(1));
                assert!(eval_circuit(bad, &c, &f).is_err());
                if external {
                    let private_links = links
                        .iter()
                        .map(|(a, b)| {
                            let read = |v: &Vec<usize>| {
                                v.iter().map(|i| i - c.raw.npublic_input).collect()
                            };
                            (read(a), read(b))
                        })
                        .collect();
                    let bits: Vec<_> = input[c.raw.npublic_input..]
                        .iter()
                        .map(|x| x.to_u128() != 0)
                        .collect();
                    let shared = crate::runtime::v2::simd_sumcheck::SharedShake::new(
                        bits.len(),
                        private_links,
                    )
                    .unwrap();
                    shared.witness(&bits).unwrap();
                }
            }
        }
    }
}

#[test]
fn scalar_checkpoint_serialization_does_not_require_initial_states() {
    use crate::{
        mldsa::runtime::reference::shake256_witness, runtime::algebra::fp24_ext6::RuntimeFp24Ext6,
    };
    let (_, witness) = shake256_witness(b"scalar witness audit", 300);
    let mut checkpoints_only = witness.clone();
    checkpoints_only.initial_states.clear();
    for k in [BinaryKeccak::default(), BinaryKeccak::legacy()] {
        assert_eq!(
            witness.bits_with_keccak(k).collect::<Vec<_>>(),
            checkpoints_only.bits_with_keccak(k).collect::<Vec<_>>()
        );
    }
    let f = RuntimeFp24Ext6::new();
    let mut expected = vec![];
    let mut actual = vec![];
    witness.push_wires_with_keccak(&f, &mut expected, BinaryKeccak::legacy());
    checkpoints_only.push_wires_with_keccak(&f, &mut actual, BinaryKeccak::legacy());
    assert_eq!(actual, expected);
}
