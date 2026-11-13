// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Independent SHA digests and malformed padding with refreshed witnesses.
use sha2::{Digest, Sha256 as Sha2Reference};

use super::sha256msg_eval::run_corruptor_test;
use crate::{
    circuits::{
        bitvec::BitvecLogic,
        sha256msg::{concrete::given, Sha256Msg},
    },
    compile::{algebra::gf2_128::Gf2_128Field, eval::FieldID, logic::eval::EvalLogic},
};

#[test]
fn sha_reference_and_rehashed_padding_attacks() {
    use sha2::{Digest, Sha256};
    let f = Gf2_128Field::new();
    // Cover every supported length for a three-block instance, not just
    // independently generated compression witnesses with the same digest code.
    for len in 0..=183 {
        let message: Vec<_> = (0..len).map(|i| (i * 29 + len) as u8).collect();
        let reference = Sha256::digest(&message);
        let expected = std::array::from_fn(|i| {
            u32::from_be_bytes(reference[4 * i..4 * i + 4].try_into().unwrap())
        });
        let tracker = crate::compile::logic::scope::AssertionScope::new();
        run_corruptor_test::<3>(&f, &tracker, &message, &|g, _| {
            g.expected_hash = expected;
        })
        .unwrap();
    }
    // Recompute every compression witness AND the output after changing
    // padding. A hash mismatch must not be the reason these are rejected.
    for len in [0, 1, 55, 56, 63, 64, 119, 120, 183] {
        let message = vec![0x53; len];
        let original = given(&message, &crate::circuits::sha256::constants::INITIAL, 3).unwrap();
        let end = original.nblocks * 64;
        let mut positions = vec![len, end - 8, end - 1];
        if len + 1 < end - 8 {
            positions.push(len + 1);
            positions.push(end - 9);
        }
        if end < 192 {
            positions.push(end);
            positions.push(191);
        }
        positions.sort_unstable();
        positions.dedup();
        for position in positions {
            for bit in 0..8 {
                let tracker = crate::compile::logic::scope::AssertionScope::new();
                let result = run_corruptor_test::<3>(&f, &tracker, &message, &|g, d| {
                    g.padded_preimage[position] ^= 1 << bit;
                    *d = crate::circuits::sha256msg::concrete::derived(g, 3);
                    g.expected_hash = d.sha_derived[g.nblocks - 1].h1;
                });
                assert!(
                    result.is_err(),
                    "padding accepted: len={len}, byte={position}, bit={bit}"
                );
                assert!(
                    result.failed_paths().iter().all(|p| {
                        !p.contains("assert_intermediate_hashes") && !p.contains("hash_eq")
                    }),
                    "the refreshed compression and final hash must agree"
                );
            }
        }
    }
}

#[test]
fn every_padding_byte_and_length_bit() {
    let f = Gf2_128Field::new();
    for len in [0, 1, 55, 56, 63, 64, 119, 120, 183] {
        let original = given(
            &vec![0x35; len],
            &crate::circuits::sha256::constants::INITIAL,
            3,
        )
        .unwrap();
        for position in len..192 {
            let mut changed = original.clone();
            changed.padded_preimage[position] ^= 1;
            let tracker = crate::compile::logic::scope::AssertionScope::new();
            let logic = EvalLogic::new(&f, &tracker);
            let bv = BitvecLogic::new(&logic);
            let wires = crate::circuits::sha256msg::evaluate_given::<_, 8>(&changed, &bv);
            let sha = Sha256Msg::<_, 3>::new(&logic);
            let pad =
                sha.assert_sha_padding(&wires.nblocks, &wires.length_bytes, &wires.padded_preimage);
            let length =
                sha.assert_length(&wires.nblocks, &wires.length_bytes, &wires.padded_preimage);
            assert!(
                pad.is_err() || length.is_err(),
                "unconstrained padding byte {position} for len={len}"
            );
        }
        for bit in 0..64 {
            let tracker = crate::compile::logic::scope::AssertionScope::new();
            let logic = EvalLogic::new(&f, &tracker);
            let bv = BitvecLogic::new(&logic);
            let mut changed = original.clone();
            changed.length_bytes ^= 1 << bit;
            let wires = crate::circuits::sha256msg::evaluate_given::<_, 8>(&changed, &bv);
            assert!(
                Sha256Msg::<_, 3>::new(&logic)
                    .assert_length(&wires.nblocks, &wires.length_bytes, &wires.padded_preimage,)
                    .is_err(),
                "length bit {bit} for len={len}"
            );
        }
    }
}

#[test]
fn compiled_v2_sha_matches_reference_and_rejects_rehashed_padding() {
    let fc = Gf2_128Field::new();
    let fr = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let (circuit, _, symbols) = crate::compile::compiler::compile_v2(&fc, |logic| {
        let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let bv = crate::circuits::bitvec::BitvecLogic::new(&logic);
        let given = crate::circuits::sha256msg::allocate_given::<_, 3>(&bv, &mut pos);
        let derived = crate::circuits::sha256msg::allocate_derived::<_, 3>(&bv, &mut pos);
        (
            Sha256Msg::<_, 3>::new(&logic).assert_message_hash(&given, &derived),
            1,
        )
    });
    let circuit = crate::compile::compiler::segment_circuit_v2(&fc, circuit);
    for length in [0, 1, 55, 56, 63, 64, 119, 120, 183] {
        let message: Vec<_> = (0..length).map(|i| (i * 37 + length) as u8).collect();
        let mut good = given(&message, &crate::circuits::sha256::constants::INITIAL, 3).unwrap();
        let reference = Sha2Reference::digest(&message);
        good.expected_hash = std::array::from_fn(|i| {
            u32::from_be_bytes(reference[4 * i..4 * i + 4].try_into().unwrap())
        });
        for bad in [false, true] {
            let mut g = good.clone();
            if bad {
                g.padded_preimage[length] ^= 1;
            }
            let derived = crate::circuits::sha256msg::derived(&g, 3);
            if bad {
                g.expected_hash = derived.sha_derived[g.nblocks - 1].h1;
            }
            let mut inputs = Vec::new();
            g.push_elements(&fr, 3, |e| inputs.push(e));
            derived.push_elements(&fr, |e| inputs.push(e));
            let result = crate::compile::eval::eval_circuit_fc(
                &fc,
                &fr,
                &circuit,
                &symbols,
                &inputs,
                FieldID::Gf2_128,
            )
            .unwrap();
            assert_eq!(
                result.is_ok(),
                !bad,
                "length={length}, malformed_padding={bad}"
            );
        }
    }
}

#[test]
fn length_is_a_numeric_witness_and_padding_is_big_endian() {
    for length in [0, 1, 55, 56, 63, 64, 256, 257] {
        let message = vec![0x53; length];
        let (blocks, bytes, padded) =
            crate::circuits::sha256msg::pad_sha256_message(&message, 6).unwrap();
        assert_eq!(bytes, length as u64);
        assert_eq!(
            &padded[blocks * 64 - 8..blocks * 64],
            &((length as u64) * 8).to_be_bytes()
        );
    }
}
