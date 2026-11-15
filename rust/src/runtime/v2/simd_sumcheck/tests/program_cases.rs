// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::proto::v2::{Circuit, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    runtime::{random::DeterministicRng, v2::proto::polygero::PolygeroConfig},
};
fn circuit() -> Circuit<F> {
    // z=(a+b+1)*b. The affine operand deliberately has a constant,
    // exercising its different native-word and bit-functional pullbacks.
    let f = F::new();
    let raw = RawCircuitBuilder {
        ninput: 4,
        npublic_input: 0,
        noutput: 1,
        logv: 0,
        constants: vec![f.one()],
        layers: vec![Layer::new(
            4,
            Stream {
                deltas: vec![Quadratic {
                    g: 0,
                    l: 3,
                    r: 1,
                    k: 0,
                }],
                segments: vec![vec![0]].into(),
                tokens: vec![0],
            },
            Stream {
                deltas: vec![Linear { g: 0, l: 2, k: 0 }],
                segments: vec![vec![0]].into(),
                tokens: vec![0],
            },
            Stream::default(),
        )],
    }
    .build();
    Circuit::from_raw(&f, raw)
}
fn forms() -> Vec<AffineInput> {
    vec![AffineInput {
        vars: vec![0, 1],
        constant: true,
    }]
}
fn program() -> Program {
    Program::new(circuit(), 3, forms(), [9; 32]).unwrap()
}
#[test]
fn complete_packed_proof_authenticates_affine_constants_and_final_seal() {
    let p = program();
    let a = 0x1234567890u128;
    let b = 0xfedcba9876u128;
    let words = vec![E::from(a), E::from(b), E::from((a ^ b ^ u128::MAX) & b)];
    let cfg = PolygeroConfig {
        k: 64,
        s: 4,
        n: 448,
        t: 24,
    };
    let proof = p
        .prove_complete(words.clone(), b"test", cfg, &mut DeterministicRng::new(14))
        .unwrap();
    p.verify_complete(&proof, b"test", cfg).unwrap();
    assert!(p.verify_complete(&proof, b"wrong", cfg).is_err());
    let other_source = Program::new(circuit(), 3, forms(), [8; 32]).unwrap();
    assert!(other_source.verify_complete(&proof, b"test", cfg).is_err());
    let mut other_forms = forms();
    other_forms[0].constant = false;
    let other_relation = Program::new(circuit(), 3, other_forms, [9; 32]).unwrap();
    assert!(other_relation
        .verify_complete(&proof, b"test", cfg)
        .is_err());

    for i in [0, 8, 40, 72, proof.len() / 2, proof.len() - 1] {
        let mut changed = proof.clone();
        changed[i] ^= 1;
        assert!(p.verify_complete(&changed, b"test", cfg).is_err());
    }
    for n in [0, 8, proof.len() / 2, proof.len() - 1] {
        assert!(p.verify_complete(&proof[..n], b"test", cfg).is_err());
    }
    let mut extra = proof.clone();
    extra.push(0);
    assert!(p.verify_complete(&extra, b"test", cfg).is_err());
    let mut bad = words;
    bad[2].xor_in_place(&E::from(1));
    assert!(p
        .prove_complete(bad, b"test", cfg, &mut DeterministicRng::new(14))
        .is_err());
}

#[test]
fn invalid_program_indices_dimensions_and_identifiers_are_rejected() {
    for mutate in [
        (|c: &mut RawCircuitBuilder<F>| c.layers[0].quadratic.deltas[0].k = 1)
            as fn(&mut RawCircuitBuilder<F>),
        |c| c.layers[0].quadratic.tokens[0] = 1,
        |c| c.layers[0].quadratic.segments[0][0] = 1,
        |c| c.layers[0].linear.deltas[0].l = 4,
        |c| c.layers[0].nw = 3,
        |c| c.noutput = 0,
    ] {
        let mut raw = circuit().into_raw().into_builder();
        mutate(&mut raw);
        let c = Circuit::from_raw(&F::new(), raw.build());
        assert!(Program::new(c, 3, forms(), [9; 32]).is_err());
    }
    assert!(Program::new(circuit(), usize::MAX, forms(), [9; 32]).is_err());
    let mut bad_forms = forms();
    bad_forms[0].vars[0] = 3;
    assert!(Program::new(circuit(), 3, bad_forms, [9; 32]).is_err());
}

#[cfg(feature = "mldsa")]
#[test]
fn shared_scalar_and_packed_claims_authenticate_the_same_cells() {
    use super::shared::ScalarClaim;
    let f = F::new();
    let cfg = PolygeroConfig {
        k: 64,
        s: 4,
        n: 448,
        t: 24,
    };
    let p = program();
    let a = 0x1234567890u128;
    let b = 0xfedcba9876u128;
    let words = vec![E::from(a), E::from(b), E::from((a ^ b ^ u128::MAX) & b)];
    let placements = [(0, 4), (1, 127), (2, 9)];
    let weights = vec![E::from(7), E::from(11), E::from(19)];
    let mut target = f.zero();
    for (&(word, bit), k) in placements.iter().zip(&weights) {
        if words[word].to_u128() >> bit & 1 != 0 {
            f.add(&mut target, k);
        }
    }
    let mask = E::from(0xaff123);
    let scalar = |coefficients: Vec<E>| ScalarClaim {
        weights: coefficients,
        rhs: NativeRow {
            constant: f.addf(&target, &mask),
            terms: vec![(p.cell_count(), f.one())],
        },
    };
    let (state, cells) = p
        .prepare_shared(words, vec![mask], &mut DeterministicRng::new(21))
        .unwrap();
    let mut pt = p.start(b"shared", cfg);
    let (proof, packing, rows) = p
        .prove_shared(
            state,
            scalar(weights.clone()),
            &placements,
            &mut pt.borrow(),
        )
        .unwrap();
    assert!(rows
        .iter()
        .all(|row| row.evaluate(&cells).unwrap() == f.zero()));
    let mut vt = p.start(b"shared", cfg);
    let replay = p
        .reduce_shared(
            &proof,
            &packing,
            scalar(weights.clone()),
            &placements,
            cells.len(),
            &mut vt.borrow(),
        )
        .unwrap();
    assert!(replay
        .iter()
        .all(|row| row.evaluate(&cells).unwrap() == f.zero()));
    assert_eq!(
        pt.append_final_seal(vec![]).into_bytes(),
        vt.append_final_seal(vec![]).into_bytes()
    );
    // Exercise the verifier's algebraic equations without a final seal. Honest
    // witness checks and damaged-proof seals must not mask an omitted equation.
    for component in 0..8 {
        let mut forged = proof.clone();
        let mut forged_packing = packing.clone();
        match component {
            0 => forged.nonlinear.xor_in_place(&f.one()),
            1 | 2 => forged.dot.rounds[0].coefficients[component - 1].xor_in_place(&f.one()),
            3 => forged.dot.cross.xor_in_place(&f.one()),
            4 | 5 => forged.dot.claims[component - 4].xor_in_place(&f.one()),
            6 => {
                if let crate::runtime::v2::proto::dual_packing::PackingProof::TraceZero {
                    u, ..
                } = &mut forged_packing
                {
                    u[0].xor_in_place(&f.one());
                }
            }
            7 => {
                if let crate::runtime::v2::proto::dual_packing::PackingProof::TraceZero {
                    a: adapter_response,
                    ..
                } = &mut forged_packing
                {
                    adapter_response.xor_in_place(&f.one());
                }
            }
            _ => unreachable!(),
        }
        let mut forged_transcript = p.start(b"shared", cfg);
        let accepted = p
            .reduce_shared(
                &forged,
                &forged_packing,
                scalar(weights.clone()),
                &placements,
                cells.len(),
                &mut forged_transcript.borrow(),
            )
            .is_ok_and(|forged_rows| {
                forged_rows
                    .iter()
                    .all(|row| row.evaluate(&cells).unwrap() == f.zero())
            });
        assert!(!accepted, "unchecked shared component {component}");
    }
    for cell in [
        p.real,
        p.pads(),
        p.masks(),
        p.masks() + 127,
        p.masks() + 128,
        p.cell_count(),
    ] {
        let mut changed = cells.clone();
        changed[cell].xor_in_place(&f.one());
        assert!(
            replay
                .iter()
                .any(|row| row.evaluate(&changed).unwrap() != f.zero()),
            "unbound shared pad {cell}"
        );
    }
    let mut changed = weights.clone();
    changed[0].xor_in_place(&f.one());
    let mut changed_transcript = p.start(b"shared", cfg);
    let changed_replay = p
        .reduce_shared(
            &proof,
            &packing,
            scalar(changed),
            &placements,
            cells.len(),
            &mut changed_transcript.borrow(),
        )
        .unwrap();
    assert!(changed_replay
        .iter()
        .any(|row| row.evaluate(&cells).unwrap() != f.zero()));
    for bad in [
        vec![(p.input_words(), 0); 3],
        vec![(0, 128); 3],
        vec![(0, 0); 2],
    ] {
        let mut malformed_transcript = p.start(b"shared", cfg);
        assert!(p
            .reduce_shared(
                &proof,
                &packing,
                scalar(weights.clone()),
                &bad,
                cells.len(),
                &mut malformed_transcript.borrow()
            )
            .is_err());
    }
}
