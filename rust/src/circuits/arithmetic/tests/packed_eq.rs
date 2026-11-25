// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        boolean::{Bitw, Boolean},
    },
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, CompileField},
        logic::{AssertionScope, Eltw, EvalLogic, Logic},
    },
};

/// Byte strings long enough to span several chunks in either field.
fn sample(len: usize, seed: u8) -> Vec<u8> {
    (0..len)
        .map(|i| (i as u8).wrapping_mul(73).wrapping_add(seed))
        .collect()
}

fn byte_bits<L: Logic>(boolean: &Boolean<'_, L>, bytes: &[u8]) -> Vec<Bitw<L>> {
    bytes
        .iter()
        .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1 == 1))
        .map(|bit| boolean.konst(bit))
        .collect()
}

fn units<L: Logic>(arith: &Arithmetic<'_, L>, bits: &[Bitw<L>], w: usize) -> Vec<Eltw<L>> {
    bits.chunks(8)
        .flat_map(|byte| arith.pack_byte_units(byte, w))
        .collect()
}

fn check_units_eq<F: CompileField>(f: &F) {
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(f, &tracker);
    let boolean = Boolean::new(&logic);
    let arith = Arithmetic::new(&logic);
    let (on, off) = (boolean.trueb(), boolean.falseb());
    for len in [1, 15, 16, 17, 31, 32, 33, 70] {
        let a = sample(len, 11);
        let a_bits = byte_bits(&boolean, &a);
        for w in [1, 2, 4, 8] {
            let a_units = units(&arith, &a_bits, w);
            assert!(arith.assert_units_eq("eq", &a_units, &a_units, w).is_ok());
            assert!(arith
                .assert_units_eq_when("eq", &on, &a_units, &a_units, w)
                .is_ok());
            for bit in 0..8 * len {
                let mut b = a.clone();
                b[bit / 8] ^= 1 << (bit % 8);
                let b_units = units(&arith, &byte_bits(&boolean, &b), w);
                let ctx = format!("len={len} w={w} bit={bit}");
                assert!(
                    arith.assert_units_eq("eq", &a_units, &b_units, w).is_err(),
                    "{ctx}"
                );
                assert!(
                    arith
                        .assert_units_eq_when("eq", &on, &a_units, &b_units, w)
                        .is_err(),
                    "{ctx}"
                );
                assert!(
                    arith
                        .assert_units_eq_when("eq", &off, &a_units, &b_units, w)
                        .is_ok(),
                    "{ctx}"
                );
            }
        }
    }
}

fn check_eq_packed_bytes<F: CompileField>(f: &F) {
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(f, &tracker);
    let boolean = Boolean::new(&logic);
    let arith = Arithmetic::new(&logic);
    let (on, off) = (boolean.trueb(), boolean.falseb());
    for len in [1, 15, 16, 17, 31, 32, 33, 70] {
        let a = sample(len, 29);
        let a_bits = byte_bits(&boolean, &a);
        let a_bytes = units(&arith, &a_bits, 8);
        assert!(arith
            .assert_eq_packed_bytes("eq", &a_bits, &a_bytes)
            .is_ok());
        assert!(arith
            .assert_eq_packed_bytes_when("eq", &on, &a_bits, &a_bytes)
            .is_ok());
        for bit in 0..8 * len {
            let mut b = a.clone();
            b[bit / 8] ^= 1 << (bit % 8);
            let b_bytes = units(&arith, &byte_bits(&boolean, &b), 8);
            let ctx = format!("len={len} bit={bit}");
            assert!(
                arith
                    .assert_eq_packed_bytes("eq", &a_bits, &b_bytes)
                    .is_err(),
                "{ctx}"
            );
            assert!(
                arith
                    .assert_eq_packed_bytes_when("eq", &on, &a_bits, &b_bytes)
                    .is_err(),
                "{ctx}"
            );
            assert!(
                arith
                    .assert_eq_packed_bytes_when("eq", &off, &a_bits, &b_bytes)
                    .is_ok(),
                "{ctx}"
            );
        }
    }
}

#[test]
fn test_units_eq_gf2_128() {
    check_units_eq(&Gf2_128Field::new());
}

#[test]
#[should_panic(expected = "invalid packed unit width")]
fn packed_equality_rejects_zero_width() {
    let f = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let arith = Arithmetic::new(&logic);
    let _ = arith.assert_units_eq("eq", &[], &[], 0);
}

#[test]
fn test_units_eq_p256() {
    check_units_eq(&P256Field::new());
}

#[test]
fn test_eq_packed_bytes_gf2_128() {
    check_eq_packed_bytes(&Gf2_128Field::new());
}

#[test]
fn test_eq_packed_bytes_p256() {
    check_eq_packed_bytes(&P256Field::new());
}
