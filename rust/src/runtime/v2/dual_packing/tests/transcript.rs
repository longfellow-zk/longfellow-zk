// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::{Digest, Sha256};

use super::super::transcript::{challenges, finish};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            packing::{binary::Binary128Extension, PackingParameters},
        },
        v2::transcript::Transcript,
    },
};

fn word(x: u64, out: &mut Vec<u8>) {
    out.extend_from_slice(&x.to_le_bytes());
}
fn bytes_value(bytes: &[u8], out: &mut Vec<u8>) {
    word(0, out);
    word(bytes.len() as u64, out);
    out.extend_from_slice(bytes);
}

fn prf_block(id: u64, parent: &[u8], counter: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(0u32.to_le_bytes());
    h.update(id.to_le_bytes());
    h.update(parent);
    h.update(counter.to_le_bytes());
    h.finalize().into()
}

/// Dual packing absorbs only `PackingU` and `PackingA`: the statement holds
/// the packing parameters and counts, and the source coefficients are never
/// absorbed.
#[test]
fn packing_messages_match_canonical_bytes() {
    let f = Gf2_128Field::new();
    let p = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    let mut actual = Transcript::for_test(b"packing-vector");
    let delta = challenges(&p, &vec![f.zero(); 128], &mut actual.borrow());
    assert_eq!(actual.round_count_for_test(), 1);

    // Independently encode the root: the test statement, then U and the
    // ROUND terminator.
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&1u32.to_le_bytes()); // STRAND
    bytes.extend_from_slice(&0u64.to_le_bytes()); // root id
    bytes.extend_from_slice(&0u32.to_le_bytes()); // no parents
    word(17, &mut bytes); // ZkStatement
    bytes_value(b"longfellow/v2/zk/transcript/v2", &mut bytes);
    bytes_value(b"packing-vector", &mut bytes);
    word(1, &mut bytes);
    word(4, &mut bytes);
    for _ in 0..4 {
        word(0, &mut bytes);
    }
    word(80, &mut bytes); // PackingU
    word(2, &mut bytes); // Elements
    word(4, &mut bytes); // GF(2^128)
    word(128, &mut bytes);
    bytes.extend_from_slice(&[0; 128 * 16]);
    word(0, &mut bytes); // ROUND
    let parent = Sha256::digest(&bytes);
    let expected = (0..64)
        .flat_map(|counter| {
            let block = prf_block(0, &parent, counter);
            [
                Gf2_128::from(u128::from_le_bytes(block[..16].try_into().unwrap())),
                Gf2_128::from(u128::from_le_bytes(block[16..].try_into().unwrap())),
            ]
        })
        .collect::<Vec<_>>();
    assert_eq!(delta, expected);

    // A follows delta, before the backend, without another boundary.
    finish(&p, &f.one(), &mut actual.borrow());
    assert_eq!(actual.round_count_for_test(), 1);
    bytes.clear();
    bytes.extend_from_slice(&1u32.to_le_bytes()); // STRAND
    bytes.extend_from_slice(&1u64.to_le_bytes()); // continuation id
    bytes.extend_from_slice(&1u32.to_le_bytes()); // one parent
    bytes.extend_from_slice(&parent);
    word(81, &mut bytes); // PackingA
    word(2, &mut bytes);
    word(4, &mut bytes);
    word(1, &mut bytes);
    bytes.extend_from_slice(&1u128.to_le_bytes());
    word(112, &mut bytes); // Seal
    bytes_value(b"body", &mut bytes);
    word(1, &mut bytes); // SEAL
    let seal = prf_block(1, &Sha256::digest(&bytes), 0);
    let mut encoded = b"body".to_vec();
    encoded.extend_from_slice(&seal);
    assert_eq!(
        actual.append_final_seal(b"body".to_vec()).into_bytes(),
        encoded
    );
}

#[test]
fn packing_binds_both_prover_messages() {
    let f = Gf2_128Field::new();
    let p = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    let run = |u0: u128, a: u128| {
        let mut ts = Transcript::for_test(b"packing-binding");
        let mut u = vec![f.zero(); 128];
        u[0] = Gf2_128::from(u0);
        let delta = challenges(&p, &u, &mut ts.borrow());
        finish(&p, &Gf2_128::from(a), &mut ts.borrow());
        (delta, ts.append_final_seal(Vec::new()).into_bytes())
    };
    let reference = run(0, 1);
    let changed_u = run(1, 1);
    assert_ne!(reference.0, changed_u.0);
    assert_ne!(reference.1, changed_u.1);
    let changed_a = run(0, 2);
    assert_eq!(reference.0, changed_a.0);
    assert_ne!(reference.1, changed_a.1);
}
