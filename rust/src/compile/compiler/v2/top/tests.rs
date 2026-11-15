// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use std::{iter::once, ops::Range};

use crate::{
    compile::{
        algebra::gf2_128::Gf2_128Field,
        compiler::{compile_v2, compile_v2_shared_inputs, segment_circuit_v2},
        logic::{Logic, LogicIO},
    },
    core::proto::v2::CircuitWriter,
};

#[test]
fn shared_input_declarations_preserve_existing_circuit_ids() {
    let f = Gf2_128Field::new();
    let (ordinary_raw, _, _) = compile_v2(&f, |l| {
        let a = l.input(1);
        let b = l.input(2);
        (l.assert0("product", &l.mul(&a, &b)), 1)
    });
    let (shared_raw, _, _) = compile_v2_shared_inputs(&f, |l| {
        let a = l.input(1);
        let b = l.input(2);
        (
            l.assert0("product", &l.mul(&a, &b)),
            1,
            once(1..3).collect(),
        )
    });
    let ordinary = segment_circuit_v2(&f, ordinary_raw);
    let shared = segment_circuit_v2(&f, shared_raw);
    assert_eq!(ordinary.id, shared.id);
    let writer = CircuitWriter::new(&f);
    assert_eq!(writer.to_bytes(&ordinary), writer.to_bytes(&shared));
}

#[test]
fn shared_inputs_retain_private_positions_before_and_after_used_input() {
    let f = Gf2_128Field::new();
    let (raw, geometry, symbols) = compile_v2_shared_inputs(&f, |l| {
        let _first = l.input(1);
        let used = l.input(2);
        let _last = l.input(3);
        (l.assert0("used", &used), 1, vec![1..2, 3..4])
    });
    assert_eq!(geometry.ninput, 3);
    assert_eq!(geometry.npublic_input, 0);
    assert_eq!(geometry.nassertions, 1);
    assert_eq!(symbols.assertion_count(), 1);
    assert_eq!(segment_circuit_v2(&f, raw).raw.ninput, 3);
}

#[test]
fn shared_inputs_cannot_cover_public_or_undeclared_positions() {
    let f = Gf2_128Field::new();
    for range in [0..1, 1..2, 2..4, Range { start: 3, end: 2 }] {
        assert!(std::panic::catch_unwind(|| {
            compile_v2_shared_inputs(&f, |l| {
                let public = l.input(1);
                let private = l.input(2);
                (l.assert_eq("equal", &public, &private), 2, vec![range])
            });
        })
        .is_err());
    }
}

#[test]
#[should_panic(expected = "some inputs are unused")]
fn unlisted_unused_private_inputs_are_rejected() {
    let f = Gf2_128Field::new();
    compile_v2_shared_inputs(&f, |l| {
        let used = l.input(1);
        let _shared = l.input(2);
        let _unlisted = l.input(3);
        (l.assert0("used", &used), 1, once(2..3).collect())
    });
}
