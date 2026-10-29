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

use super::mdoc_signature_corruptors;
use crate::{
    compile::algebra::{p256::P256Field, secp256r1::Secp256r1},
    core::algebra::{AlgebraicField, Nat, SupportsNatConversions},
    mdoc::circuits::{
        config::K_ZSTD_LEVEL,
        parse_test_data,
        signature::{
            derived, given, signature_input_of_parsed_mdoc, ConcreteDerived, ConcreteGiven,
            MdocSignature, SignatureMac,
        },
        MdocSigCompileField,
    },
};

fn test_mdoc_zk_circuits_signature_generic(
    fc: &P256Field,
    _fr: &crate::runtime::algebra::p256::P256Field,
) {
    let curve_c = Secp256r1::new(fc);
    let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;

    let (_circuit, stats, _symbols) = super::compile(fc, |iologic| {
        let mdoc_sig = MdocSignature::new(&iologic, &curve_c);
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let given_wires = crate::mdoc::circuits::signature::allocate_given(&iologic, &bv, &mut pos);
        let derived_wires = crate::mdoc::circuits::signature::allocate_derived(&iologic, &mut pos);

        (
            mdoc_sig.assert_signatures_and_macs(&given_wires, &derived_wires),
            1,
            0,
        )
    });
    assert_eq!(
        stats,
        crate::compile::eval::CircuitGeometry {
            ninput: 4772,
            npublic_input: 0,
            noutput: 6,
            nlayers: 19,
            nwires: 167721,
            nterms: 259533,
            nassertions: 4796,
        }
    );
}

#[test]
fn test_mdoc_zk_circuits_signature() {
    let fc = P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    test_mdoc_zk_circuits_signature_generic(&fc, &fr);
}

fn mdoc_zk_circuits_signature_circuit<FC>(
    fc: &FC,
) -> (
    crate::compile::eval::Circuit<FC>,
    crate::compile::eval::CircuitGeometry,
)
where FC: MdocSigCompileField {
    let (circuit, stats, _) = compile_signature_circuit(fc);
    (circuit, stats)
}

fn compile_signature_circuit<FC>(
    fc: &FC,
) -> (
    crate::compile::eval::Circuit<FC>,
    crate::compile::eval::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where FC: MdocSigCompileField {
    let curve_c = Secp256r1::new(fc);
    let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;

    super::compile(fc, |iologic| {
        let mdoc_sig = MdocSignature::new(&iologic, &curve_c);
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let given_wires = crate::mdoc::circuits::signature::allocate_given(&iologic, &bv, &mut pos);
        let derived_wires = crate::mdoc::circuits::signature::allocate_derived(&iologic, &mut pos);

        (
            mdoc_sig.assert_signatures_and_macs(&given_wires, &derived_wires),
            1,
            0,
        )
    })
}

fn push_nat_bits<F: AlgebraicField, N: Nat<4>>(
    inputs: &mut Vec<F::E>,
    value: &N,
    nbits: usize,
    f: &F,
) {
    let bytes = value.to_bytes_le();
    for bit in 0..nbits {
        let bit_val = bytes.get(bit / 8).map_or(0, |byte| (byte >> (bit % 8)) & 1);
        inputs.push(if bit_val == 1 { f.one() } else { f.zero() });
    }
}

fn push_u128_bits<F: AlgebraicField>(inputs: &mut Vec<F::E>, value: u128, f: &F) {
    for bit in 0..128 {
        inputs.push(if (value >> bit) & 1 == 1 {
            f.one()
        } else {
            f.zero()
        });
    }
}

fn push_ecdsa_given<F: AlgebraicField>(
    inputs: &mut Vec<F::E>,
    given: &crate::circuits::ecdsa2::concrete::ConcreteGiven<F>,
) {
    inputs.push(given.pkxy.0.clone());
    inputs.push(given.pkxy.1.clone());
    inputs.push(given.e.clone());
    inputs.push(given.rxy.0.clone());
    inputs.push(given.rxy.1.clone());
    inputs.extend(given.ers.iter().cloned());
}

fn make_signature_inputs<F>(
    given: &ConcreteGiven<F, <F as SupportsNatConversions<4>>::N>,
    derived: &ConcreteDerived<F>,
    f: &F,
) -> Vec<F::E>
where
    F: crate::runtime::algebra::field::RuntimeField<4> + SupportsNatConversions<4>,
{
    let mut inputs = crate::compile::eval::initial_inputs(f);

    inputs.push(given.issuer_sig_given.pkxy.0.clone());
    inputs.push(given.issuer_sig_given.pkxy.1.clone());
    push_nat_bits(&mut inputs, &given.sig_input.issuer_sig_e, 256, f);
    push_ecdsa_given(&mut inputs, &given.issuer_sig_given);

    push_nat_bits(&mut inputs, &given.sig_input.device_pk.0, 256, f);
    push_nat_bits(&mut inputs, &given.sig_input.device_pk.1, 256, f);
    push_nat_bits(&mut inputs, &given.sig_input.device_sig_e, 256, f);
    push_ecdsa_given(&mut inputs, &given.device_sig_given);

    for value in given
        .mac_e
        .iter()
        .chain(&given.mac_device_pkx)
        .chain(&given.mac_device_pky)
    {
        push_u128_bits(&mut inputs, *value, f);
    }
    push_u128_bits(&mut inputs, given.mac_input.mac_av, f);
    for pair in given.mac_input.mac_ap {
        push_u128_bits(&mut inputs, pair[0], f);
        push_u128_bits(&mut inputs, pair[1], f);
    }

    derived.push_derived(|value| inputs.push(value));
    inputs
}

#[test]
fn test_compile_mdoc_signature_corruptors() {
    let fc = P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let curve = crate::runtime::algebra::secp256r1::Secp256r1::new(&fr);
    let fn_field = crate::runtime::algebra::Q256Field::new();
    let (circuit, _, symbols) = compile_signature_circuit(&fc);

    let (issuer_pk, parsed, _) = parse_test_data::<4, crate::runtime::algebra::RuntimeNat<4>>(
        &crate::mdoc::testcases::vectors::TEST_DATA,
    );
    let base_sig_input = signature_input_of_parsed_mdoc(&parsed, issuer_pk);
    let base_mac_input = SignatureMac {
        mac_av: 0x112233445566778899aabbccddeeff00,
        mac_ap: [[
            0xabcdef0123456789abcdef0123456789,
            0xfedcba9876543210fedcba9876543210,
        ]; 3],
    };

    let valid_given = given::<4, _, _, _>(
        base_sig_input.clone(),
        base_mac_input.clone(),
        &fr,
        &fn_field,
        &curve,
    );
    let valid_derived = derived::<4, _, _, _>(&fr, &fn_field, &curve, &valid_given).unwrap();
    crate::compile::eval::eval_circuit_fc(
        &fc,
        &fr,
        &circuit,
        &symbols,
        &make_signature_inputs(&valid_given, &valid_derived, &fr),
        crate::compile::eval::FieldID::P256,
    )
    .unwrap()
    .assert_all_passed();

    for corruptor in mdoc_signature_corruptors::all_mdoc_signature_corruptors::<
        crate::runtime::algebra::p256::P256Field,
    >() {
        let mut sig_input = base_sig_input.clone();
        if let Some(corrupt_input) = &corruptor.corrupt_input {
            corrupt_input(&mut sig_input);
        }
        let mut given =
            given::<4, _, _, _>(sig_input, base_mac_input.clone(), &fr, &fn_field, &curve);
        let derived = derived::<4, _, _, _>(&fr, &fn_field, &curve, &given).unwrap();
        if let Some(corrupt_given) = &corruptor.corrupt_given {
            corrupt_given(&mut given, &fr);
        }

        let result = crate::compile::eval::eval_circuit_fc(
            &fc,
            &fr,
            &circuit,
            &symbols,
            &make_signature_inputs(&given, &derived, &fr),
            crate::compile::eval::FieldID::P256,
        )
        .unwrap();
        let failed = result.failed_paths();
        let expected_path = &corruptor.expected_path;
        assert!(
            failed.iter().any(|path| path == expected_path),
            "Corruptor '{}' expected exact compiled failure path '{}', actual failures: {failed:?}",
            corruptor.name,
            expected_path
        );
    }
}

#[test]
fn test_serialize_and_verify_mdoc_signature_circuit() {
    use crate::core::proto::{writer::CircuitWriter, FieldID};

    let p256_c = P256Field::new();
    let (circuit, _stats) = mdoc_zk_circuits_signature_circuit(&p256_c);

    let expected_id: [u8; 32] = [
        222, 193, 89, 34, 205, 161, 229, 3, 216, 142, 163, 182, 242, 67, 127, 151, 161, 229, 202,
        254, 169, 54, 226, 145, 29, 223, 137, 212, 185, 98, 238, 221,
    ];
    assert_eq!(
        circuit.id, expected_id,
        "Circuit hash changed! Expected {:?}, got {:?}",
        expected_id, circuit.id
    );

    let writer = CircuitWriter::new(&p256_c, FieldID::P256);
    let serialized = writer.to_bytes_lfc3(&circuit);
    let _compressed =
        zstd::bulk::compress(&serialized, K_ZSTD_LEVEL).expect("zstd compression failed");
}
