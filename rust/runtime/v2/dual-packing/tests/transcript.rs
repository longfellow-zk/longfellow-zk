// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

use super::transcript::{begin, challenges, finish};
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

fn frame(bytes: &[u8], out: &mut Vec<u8>) {
    out.push(0);
    out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(bytes);
}

#[test]
fn packing_statement_matches_canonical_bytes_without_source_coefficients() {
    let f = Gf2_128Field::new();
    let p = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    for statement in [&b""[..], &[42; 32][..]] {
        let mut actual = Transcript::new(b"packing-vector");
        // A large source needs only its count here, with no coefficient array.
        begin(&p, statement, 1_000_001, 7, &mut actual.borrow());
        let delta = challenges(&p, &vec![f.zero(); 128], &mut actual.borrow());
        assert_eq!(actual.round_count_for_test(), 1);

        // Independently encode the same bytes as WireBlocks.packingStatement,
        // followed by U and the round footer. There is no RHS or term stream.
        let mut bytes = Vec::new();
        for value in [
            &b"longfellow/transcript/v2"[..],
            &b"packing-vector"[..],
            &b"longfellow/dual-packing128/trace-zero/v1"[..],
            statement,
            &2u32.to_le_bytes()[..],
            &1_000_001u64.to_le_bytes()[..],
            &7u64.to_le_bytes()[..],
        ] {
            frame(value, &mut bytes);
        }
        bytes.push(2); // write_elt_field_slice(U)
        bytes.extend_from_slice(&128u64.to_le_bytes());
        bytes.extend_from_slice(&[0; 128 * 16]);
        frame(b"longfellow/transcript/v2/round", &mut bytes);
        frame(&[5], &mut bytes); // Packing
        frame(&0u64.to_le_bytes(), &mut bytes);
        let mut hash = Shake256::default();
        hash.update(&bytes);
        let mut reader = hash.finalize_xof();
        let mut link = [0; 32];
        reader.read(&mut link);
        let expected = (0..128)
            .map(|_| {
                let mut cell = [0; 16];
                reader.read(&mut cell);
                Gf2_128::from(u128::from_le_bytes(cell))
            })
            .collect::<Vec<_>>();
        assert_eq!(delta, expected);

        // A is bound after delta, before the backend, without another round.
        finish(&p, &f.one(), &mut actual.borrow());
        assert_eq!(actual.round_count_for_test(), 1);
        frame(b"longfellow/transcript/v2/boundary-output", &mut bytes);
        frame(&link, &mut bytes);
        frame(b"trace-zero128/A", &mut bytes);
        bytes.push(1); // write_elt_field(A)
        bytes.extend_from_slice(&1u128.to_le_bytes());
        frame(b"longfellow/transcript/v2/final", &mut bytes);
        frame(&1u64.to_le_bytes(), &mut bytes);
        frame(b"body", &mut bytes);
        let mut final_hash = Shake256::default();
        final_hash.update(&bytes);
        let mut seal = [0; 32];
        final_hash.finalize_xof().read(&mut seal);
        let mut encoded = b"body".to_vec();
        encoded.extend_from_slice(&seal);
        assert_eq!(
            actual.append_final_seal(b"body".to_vec()).into_bytes(),
            encoded
        );
    }
}

#[test]
fn packing_binds_statement_layout_and_both_prover_messages() {
    let f = Gf2_128Field::new();
    let p = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    let run = |statement: &[u8], inputs, auxiliary, u0: u128, a: u128| {
        let mut ts = Transcript::new(b"packing-binding");
        begin(&p, statement, inputs, auxiliary, &mut ts.borrow());
        let mut u = vec![f.zero(); 128];
        u[0] = Gf2_128::from(u0);
        let delta = challenges(&p, &u, &mut ts.borrow());
        finish(&p, &Gf2_128::from(a), &mut ts.borrow());
        (delta, ts.append_final_seal(Vec::new()).into_bytes())
    };
    let reference = run(b"", 17, 3, 0, 1);
    for changed in [
        run(b"circuit-id", 17, 3, 0, 1),
        run(b"", 18, 3, 0, 1),
        run(b"", 17, 4, 0, 1),
        run(b"", 17, 3, 1, 1),
    ] {
        assert_ne!(reference.0, changed.0);
        assert_ne!(reference.1, changed.1);
    }
    let changed_a = run(b"", 17, 3, 0, 2);
    assert_eq!(reference.0, changed_a.0);
    assert_ne!(reference.1, changed_a.1);
}
