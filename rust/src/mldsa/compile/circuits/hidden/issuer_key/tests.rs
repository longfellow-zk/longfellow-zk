// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    compile::{
        algebra::gf2_128::Gf2_128Field as CF,
        compiler::{compile_v2, segment_circuit_v2},
        logic::K_FIRST_WIRE_POSITION,
    },
    core::{
        algebra::AlgebraicField,
        proto::v2::{CircuitReader, CircuitWriter},
    },
    mldsa::{
        proto::MlDsa44,
        runtime::reference::{
            decode_public_key, rejection_sample_ntt_polynomial, shake128_witness,
        },
    },
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field as RF},
        v2::sumcheck::eval_circuit,
    },
};
#[derive(Clone, Copy, Default)]
struct Tiny;
impl MlDsaParams for Tiny {
    const K: usize = 1;
    const L: usize = 1;
    const TAU: usize = MlDsa44::TAU;
    const OMEGA: usize = MlDsa44::OMEGA;
    const C_TILDE_BYTES: usize = MlDsa44::C_TILDE_BYTES;
    const GAMMA1: u32 = MlDsa44::GAMMA1;
    const GAMMA2: u32 = MlDsa44::GAMMA2;
    const REJECTION_BOUND: u32 = MlDsa44::REJECTION_BOUND;
    const Z_BITS: usize = MlDsa44::Z_BITS;
    const R1_BITS: usize = MlDsa44::R1_BITS;
    const W1_BYTES: usize = MlDsa44::W1_BYTES;
}
#[test]
fn hidden_issuer_expansion_rejects_matrix_seed_counter_and_state_mutations() {
    let cf = CF::new();
    let (unsegmented, _, _) = compile_v2(&cf, |logic| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let gamma: Vec<_> = (0..2).map(|_| logic.next(&mut pos)).collect();
        let public = pos;
        let (bits, mut checks, _) =
            allocate_issuer_key::<_, Tiny>(&logic, &mut pos, &gamma, BinaryKeccak::default());
        let b = Boolean::new(&logic);
        checks.extend(
            bits[23 * N..]
                .iter()
                .map(|bit| logic.assert0("test_t1_zero", &b.as_eltw(bit))),
        );
        (logic.assert_all("hidden_key", &checks), public)
    });
    let compiled = segment_circuit_v2(&cf, unsegmented);
    let bytes = CircuitWriter::new(&cf).to_bytes(&compiled);
    let f = RF::new();
    let (c, tail) = CircuitReader::new(&f).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    let mut rho = vec![0u8; 32];
    let (output, trace, seed) = loop {
        let mut seed = rho.clone();
        seed.extend([0, 0]);
        let (output, trace) = shake128_witness(&seed, REJ_NTT_BYTES);
        if output.as_chunks::<3>().0.iter().any(|x| {
            (u32::from(x[0]) | (u32::from(x[1]) << 8) | (u32::from(x[2] & 127) << 16)) >= Q
        }) {
            break (output, trace, seed);
        }
        rho[0] = rho[0].wrapping_add(1);
    };
    let polynomial = rejection_sample_ntt_polynomial(&seed).unwrap();
    let mut key = rho.clone();
    key.extend(vec![0; 320]);
    let decoded = decode_public_key::<Tiny>(&key).unwrap();
    assert_eq!(polynomial, decoded.a_hat[0][0]);
    let mut input = vec![Gf2_128::from(137), Gf2_128::from(9571)];
    let mut append =
        |x: u32, n: usize| input.extend((0..n).map(|r| Gf2_128::from(u128::from(x >> r & 1))));
    for x in polynomial {
        append(x, 23);
    }
    for _ in 0..N {
        append(0, 10);
    }
    for x in rho {
        append(u32::from(x), 8);
    }
    let state_start = input.len();
    trace.push_wires_with_keccak(&f, &mut input, BinaryKeccak::default());
    let count_start = input.len();
    let mut count = 0u32;
    for x in output.as_chunks::<3>().0 {
        let value = u32::from(x[0]) | (u32::from(x[1]) << 8) | (u32::from(x[2] & 127) << 16);
        count += u32::from(value < Q);
        input.extend((0..9).map(|r| Gf2_128::from(u128::from(count >> r & 1))));
    }
    assert_eq!(input.len(), c.raw.ninput);
    assert!(eval_circuit(input.clone(), &c, &f).is_ok());
    for at in [
        2,
        2 + 23 * N + 10 * N,
        state_start,
        count_start,
        input.len() - 1,
    ] {
        let mut bad = input.clone();
        f.add(&mut bad[at], &f.one());
        assert!(eval_circuit(bad, &c, &f).is_err(), "mutation {at}");
    }
    let mut bad = input;
    bad[2] = Gf2_128::from(2);
    assert!(eval_circuit(bad, &c, &f).is_err());
}
