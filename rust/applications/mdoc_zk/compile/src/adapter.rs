// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! MAC-free mdoc circuits. Shared input bits are reused by the binary adapter.
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::V256,
        boolean::Boolean,
        ecdsa2::{EcdsaCircuit, Given},
    },
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, secp256r1::Secp256r1},
        compiler::{compile_v2, segment_circuit_v2},
        logic::{Logic, LogicIO, K_FIRST_WIRE_POSITION},
    },
    core::proto::v2::Circuit,
    mdoc::circuits::{hash::circuit::MdocHash, p256_adapter::MODULUS},
};
pub fn native_circuit(f: &P256Field) -> Circuit<P256Field> {
    let (c, _, _) = compile_v2(f, |logic| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let issuer_pk = (logic.next(&mut pos), logic.next(&mut pos));
        let b = Boolean::new(&logic);
        // The verifier constructs device_e from a public digest. The external
        // adapter ties the other 768 inputs to packed binary source bits.
        // Prime-field inputs retain their bit assertions, and the signature
        // gadget checks the exact digest and integer ranges.
        let next_bit = |pos: &mut usize| b.of_input_eltw(logic.next(pos));
        let device_e = V256::new((0..256).map(|_| next_bit(&mut pos)).collect());
        let npublic = pos;
        let issuer_e = V256::new((0..256).map(|_| next_bit(&mut pos)).collect());
        let device_pk = (
            V256::new((0..256).map(|_| next_bit(&mut pos)).collect()),
            V256::new((0..256).map(|_| next_bit(&mut pos)).collect()),
        );
        let arithmetic = Arithmetic::new(&logic);
        let mut given = |pkxy, e| {
            let rxy = (logic.next(&mut pos), logic.next(&mut pos));
            let ers = std::array::from_fn(|_| logic.next(&mut pos));
            Given { pkxy, e, rxy, ers }
        };
        let issuer = given(issuer_pk, arithmetic.as_eltw_unsafe(issuer_e.as_array()));
        let device = given(
            (
                arithmetic.as_eltw_unsafe(device_pk.0.as_array()),
                arithmetic.as_eltw_unsafe(device_pk.1.as_array()),
            ),
            arithmetic.as_eltw_unsafe(device_e.as_array()),
        );
        let issuer_derived = crate::circuits::ecdsa2::allocate_derived_wires(&logic, &mut pos);
        let device_derived = crate::circuits::ecdsa2::allocate_derived_wires(&logic, &mut pos);
        let curve = Secp256r1::new(f);
        let ecdsa = EcdsaCircuit::new(&logic, &curve);
        (
            logic.assert_all(
                "mdoc_adapter_signatures",
                &[
                    ecdsa.assert_signature_on_digest(&issuer, &issuer_derived, &issuer_e),
                    ecdsa.assert_signature_on_digest(&device, &device_derived, &device_e),
                ],
            ),
            npublic,
        )
    });
    segment_circuit_v2(f, c)
}
pub fn binary_circuit(f: &Gf2_128Field, num_attrs: usize) -> Result<Circuit<Gf2_128Field>, String> {
    if !(1..=4).contains(&num_attrs) {
        return Err("adapter attribute count".into());
    }
    let (c, _, _) = compile_v2(f, |l| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let (given, derived, npublic) =
            crate::mdoc::circuits::hash::allocate(&l, num_attrs, &mut pos);
        let b = Boolean::new(&l);
        let a = Arithmetic::new(&l);
        let modulus: Vec<_> = (0..256)
            .map(|r| b.konst((MODULUS[r / 64] >> (r % 64)) & 1 != 0))
            .collect();
        (
            l.assert_all(
                "mdoc_hash_and_adapter",
                &[
                    MdocHash::new(&l, num_attrs).assert_valid_presentation(&given, &derived),
                    b.assert_true(
                        "canonical_device_x",
                        &a.lt(given.device_pk.0.as_array(), &modulus),
                    ),
                    b.assert_true(
                        "canonical_device_y",
                        &a.lt(given.device_pk.1.as_array(), &modulus),
                    ),
                ],
            ),
            npublic,
        )
    });
    // Archived at its natural width. The link's mask, quotient pads and tree
    // leaves live beyond this width in the shared input array, so this
    // circuit cannot address them.
    Ok(segment_circuit_v2(f, c.into_builder().build()))
}
