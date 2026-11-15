// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exhaustive relation audit for both bounded UseHint parameter sets.
use super::*;
use crate::{
    circuits::boolean::BooleanIO,
    compile::{
        algebra::gf2_128::Gf2_128Field as CF,
        compiler::{compile_v2, segment_circuit_v2},
    },
    core::proto::v2::{CircuitReader, CircuitWriter},
    mldsa::proto::{MlDsa44, MlDsa65},
    runtime::{
        algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as RF},
        v2::sumcheck::eval_circuit,
    },
};
fn check<P: MlDsaParams>() {
    let cf = CF::new();
    let (unsegmented, _, _) = compile_v2(&cf, |l| {
        let io = BooleanIO::new(&l);
        let mut pos = 1;
        let hint = io.next(&mut pos);
        let raw: Vec<_> = (0..P::R1_BITS).map(|_| io.next(&mut pos)).collect();
        let sign = io.next(&mut pos);
        let hinted: Vec<_> = (0..P::R1_BITS).map(|_| io.next(&mut pos)).collect();
        (
            assert_hint_relation::<_, P>(&l, &hint, &raw, &sign, &hinted),
            1,
        )
    });
    let compiled = segment_circuit_v2(&cf, unsegmented);
    let bytes = CircuitWriter::new(&cf).to_bytes(&compiled);
    let f = RF::new();
    let (c, tail) = CircuitReader::new(&f).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    let m = P::use_hint_modulus();
    for raw in 0..m {
        for nonpositive in [false, true] {
            for hint in [false, true] {
                let expected = if !hint {
                    raw
                } else if nonpositive {
                    (raw + m - 1) % m
                } else {
                    (raw + 1) % m
                };
                for candidate in 0..1 << P::R1_BITS {
                    let mut input = vec![E::from(u128::from(hint))];
                    input.extend((0..P::R1_BITS).map(|r| E::from(u128::from(raw >> r & 1))));
                    input.push(E::from(u128::from(nonpositive)));
                    input.extend((0..P::R1_BITS).map(|r| E::from(u128::from(candidate >> r & 1))));
                    assert_eq!(eval_circuit(input,&c,&f).is_ok(),candidate==expected,
                "UseHint K={} raw={raw} nonpositive={nonpositive} hint={hint} candidate={candidate}",P::K);
                }
            }
        }
    }
}
#[test]
fn use_hint_44_exhausts_every_bounded_input_and_output() {
    check::<MlDsa44>();
}
#[test]
fn use_hint_65_exhausts_every_bounded_input_and_output() {
    check::<MlDsa65>();
}
