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

use super::test_support;
use crate::{
    circuits::{
        analog_adder::FieldWrappingSum,
        sha256::{derived, ConcreteDerived, ConcreteGiven, Sha256},
    },
    compile::{
        algebra::{field::CompileField, gf2_128::Gf2_128Field, p256::P256Field},
        eval::FieldID,
    },
    core::algebra::SerializableField,
    runtime::algebra::field::RuntimeField,
};

fn push_u32_bits<const W: usize, FR: RuntimeField<W>>(inputs: &mut Vec<FR::E>, val: u32, fr: &FR) {
    for k in 0..32 {
        let bit = (val >> k) & 1;
        inputs.push(if bit == 1 { fr.one() } else { fr.zero() });
    }
}

fn make_inputs<const W: usize, FR: RuntimeField<W>>(
    given: &ConcreteGiven,
    derived: &ConcreteDerived,
    fr: &FR,
) -> Vec<FR::E> {
    let mut inputs = crate::compile::eval::initial_inputs(fr);
    for &val in &given.input_block {
        push_u32_bits(&mut inputs, val, fr);
    }
    for &val in &given.h0 {
        push_u32_bits(&mut inputs, val, fr);
    }
    for &val in &derived.outw {
        push_u32_bits(&mut inputs, val, fr);
    }
    for &val in &derived.oute {
        push_u32_bits(&mut inputs, val, fr);
    }
    for &val in &derived.outa {
        push_u32_bits(&mut inputs, val, fr);
    }
    for &val in &derived.h1 {
        push_u32_bits(&mut inputs, val, fr);
    }
    inputs
}

fn test_compile_sha256_for_field<
    'a,
    const W: usize,
    FC: CompileField + FieldWrappingSum + SerializableField,
    FR: RuntimeField<W> + SerializableField,
>(
    fc: &'a FC,
    fr: &'a FR,
    name: &str,
    field_id: FieldID,
    expected_stats: crate::compile::eval::CircuitGeometry,
) {
    let input = [
        0, 0xdeadbeef, 0xbd5b7dde, 0x9c093ccd, 0x7ab6fbbc, 0x5964baab, 0x3812799a, 0x16c03889,
        0xf56df778, 0xd41bb667, 0xb2c97556, 0x91773445, 0x7024f334, 0x4ed2b223, 0x2d807112,
        0xc2e3001,
    ];
    let h0 = [
        0, 0xabadcafe, 0x575b95fc, 0x30960fa, 0xaeb72bf8, 0x5a64f6f6, 0x612c1f4, 0xb1c08cf2,
    ];
    let given = ConcreteGiven {
        input_block: input,
        h0,
    };
    let derived_val = derived(&given);

    let (circuit, stats, symbols) = super::compile(fc, |iologic| {
        let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let sha256 = Sha256::new(&iologic);
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let given_wires = crate::circuits::sha256::allocate_given(&bv, &mut pos);
        let derived_wires = crate::circuits::sha256::allocate_derived(&bv, &mut pos);

        (
            sha256.assert_transform_block(&given_wires, &derived_wires),
            1,
            0,
        )
    });

    crate::compile::compiler::dump_stats(name, &circuit, &stats);

    assert_eq!(stats, expected_stats);

    // Verify valid compile-time circuit evaluation
    let inputs = make_inputs(&given, &derived_val, fr);
    crate::compile::eval::eval_circuit_fc(fc, fr, &circuit, &symbols, &inputs, field_id)
        .unwrap()
        .assert_all_passed();
}

#[test]
fn test_compile_sha256() {
    let p256_c = P256Field::new();
    let p256_r = crate::runtime::algebra::p256::P256Field::new();
    test_compile_sha256_for_field::<4, _, _>(
        &p256_c,
        &p256_r,
        "sha256_p256",
        FieldID::P256,
        crate::compile::eval::CircuitGeometry {
            ninput: 6656,
            npublic_input: 0,
            noutput: 128,
            nlayers: 6,
            nwires: 30295,
            nterms: 118055,
            nassertions: 6840,
        },
    );
    let gf2_c = Gf2_128Field::new();
    let gf2_r = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    test_compile_sha256_for_field::<2, _, _>(
        &gf2_c,
        &gf2_r,
        "sha256_gf2_128",
        FieldID::Gf2_128,
        crate::compile::eval::CircuitGeometry {
            ninput: 6656,
            npublic_input: 0,
            noutput: 128,
            nlayers: 12,
            nwires: 51408,
            nterms: 98928,
            nassertions: 6840,
        },
    );
}

#[test]
fn test_compile_sha256_tampering() {
    let fc = P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let input = [
        0, 0xdeadbeef, 0xbd5b7dde, 0x9c093ccd, 0x7ab6fbbc, 0x5964baab, 0x3812799a, 0x16c03889,
        0xf56df778, 0xd41bb667, 0xb2c97556, 0x91773445, 0x7024f334, 0x4ed2b223, 0x2d807112,
        0xc2e3001,
    ];
    let h0 = [
        0, 0xabadcafe, 0x575b95fc, 0x30960fa, 0xaeb72bf8, 0x5a64f6f6, 0x612c1f4, 0xb1c08cf2,
    ];
    let given = ConcreteGiven {
        input_block: input,
        h0,
    };
    let derived_val = derived(&given);

    let (circuit, _stats, symbols) = super::compile(&fc, |iologic| {
        let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let sha256 = Sha256::new(&iologic);
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let given_wires = crate::circuits::sha256::allocate_given(&bv, &mut pos);
        let derived_wires = crate::circuits::sha256::allocate_derived(&bv, &mut pos);

        (
            sha256.assert_transform_block(&given_wires, &derived_wires),
            1,
            0,
        )
    });

    let corruptors = test_support::all_sha256_corruptors();

    for c in corruptors {
        let mut g = given.clone();
        let mut d = derived_val.clone();
        (c.corrupt)(&mut g, &mut d);

        let inputs = make_inputs(&g, &d, &fr);
        let eval_res = crate::compile::eval::eval_circuit_fc(
            &fc,
            &fr,
            &circuit,
            &symbols,
            &inputs,
            FieldID::P256,
        )
        .unwrap();
        assert!(
            eval_res.is_err(),
            "Corruptor '{}' failed to cause circuit evaluation error",
            c.name
        );
    }
}
