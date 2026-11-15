// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc v2 circuits. The signature circuit's issuer digest and device
//! key inputs are stored as bits of the hash circuit's witness (foreign
//! storage); the hash circuit also checks that the device key is canonical.
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::V256,
        boolean::{Boolean, BooleanIO},
        ecdsa2::{Derived, EcdsaCircuit, Given},
    },
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, secp256r1::Secp256r1},
        compiler::{compile_v2, segment_circuit_v2},
        logic::{Logic, LogicIO, K_FIRST_WIRE_POSITION},
    },
    core::{
        algebra::{
            encoding::P256_MODULUS, AlgebraicField, HasLookupPoints, SupportsU64Conversions,
        },
        proto::v2::Circuit,
    },
    mdoc::{
        circuits::hash::{allocate, allocate_without_structure, MdocHash},
        proto::{layout, NEXT_MAX_ATTRIBUTES},
    },
};
pub fn native_circuit(f: &P256Field) -> Circuit<P256Field> {
    for index in 0..1usize << layout::sig::ERS_BITS {
        let expected = f.subf(
            &f.u64_to_element(layout::sig::ERS_SCALE.unsigned_abs() * index as u64),
            &f.u64_to_element(layout::sig::ERS_OFFSET.unsigned_abs()),
        );
        assert_eq!(
            f.lookup_point(layout::sig::ERS_TABLE_SIZE, index),
            expected,
            "signature ERS affine lookup contract"
        );
    }
    let (c, _, _) = compile_v2(f, |logic| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let issuer_pk = (logic.next(&mut pos), logic.next(&mut pos));
        let bits = BooleanIO::new(&logic);
        // The verifier constructs device_e from a public digest. Foreign storage
        // keeps the other 768 inputs as bits of the hash witness.
        // Prime-field inputs retain their bit assertions, and the signature
        // gadget checks the exact digest and integer ranges.
        let next_bit = |pos: &mut usize| bits.next(pos);
        let device_e = V256::new((0..256).map(|_| next_bit(&mut pos)).collect());
        let npublic = pos;
        // The leading private inputs follow the shared layout table, which
        // the runtime link reads; a drift here must fail compilation.
        let at = |pos: usize, range: &core::ops::Range<usize>, name: &str| {
            if let Err(e) = layout::check_at(pos - npublic, range, name) {
                panic!("{e}");
            }
        };
        let bits256 = |pos: &mut usize| V256::new((0..256).map(|_| next_bit(pos)).collect());
        at(pos, &layout::sig::ISSUER_DIGEST, "issuer digest");
        let issuer_e = bits256(&mut pos);
        at(pos, &layout::sig::DEVICE_X, "device x");
        let device_x = bits256(&mut pos);
        at(pos, &layout::sig::DEVICE_Y, "device y");
        let device_pk = (device_x, bits256(&mut pos));
        at(
            pos,
            &(layout::SHARED_BITS..layout::SHARED_BITS),
            "end of shared inputs",
        );
        let arithmetic = Arithmetic::new(&logic);
        let mut given =
            |pkxy, e, r_range: &core::ops::Range<usize>, ers_range: &core::ops::Range<usize>| {
                at(pos, r_range, "signature R");
                let given = Given::from_fn_with_key(pkxy, e, || logic.next(&mut pos));
                at(pos, &(ers_range.end..ers_range.end), "end of signature ERS");
                given
            };
        let issuer = given(
            issuer_pk,
            arithmetic.as_eltw_unsafe(issuer_e.as_array()),
            &layout::sig::ISSUER_R,
            &layout::sig::ISSUER_ERS,
        );
        let device = given(
            (
                arithmetic.as_eltw_unsafe(device_pk.0.as_array()),
                arithmetic.as_eltw_unsafe(device_pk.1.as_array()),
            ),
            arithmetic.as_eltw_unsafe(device_e.as_array()),
            &layout::sig::DEVICE_R,
            &layout::sig::DEVICE_ERS,
        );
        let issuer_derived = Derived::from_fn(|| logic.next(&mut pos));
        let device_derived = Derived::from_fn(|| logic.next(&mut pos));
        let curve = Secp256r1::new(f);
        let ecdsa = EcdsaCircuit::new(&logic, &curve);
        (
            logic.assert_all(
                "mdoc_signatures",
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
    binary_circuit_impl(f, num_attrs, true)
}

/// The original v2 byte-offset predicate, with no structural parser.
pub fn parser_free_binary_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<Circuit<Gf2_128Field>, String> {
    binary_circuit_impl(f, num_attrs, false)
}

fn binary_circuit_impl(
    f: &Gf2_128Field,
    num_attrs: usize,
    structural: bool,
) -> Result<Circuit<Gf2_128Field>, String> {
    if !(1..=NEXT_MAX_ATTRIBUTES).contains(&num_attrs) {
        return Err("hash circuit attribute count".into());
    }
    let (c, _, _) = compile_v2(f, |l| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let (given, derived, npublic) = if structural {
            allocate(&l, num_attrs, &mut pos)
        } else {
            allocate_without_structure(&l, num_attrs, &mut pos)
        };
        let b = Boolean::new(&l);
        let a = Arithmetic::new(&l);
        let modulus: Vec<_> = (0..256)
            .map(|r| b.konst((P256_MODULUS[r / 8] >> (r % 8)) & 1 != 0))
            .collect();
        (
            l.assert_all(
                "mdoc_hash",
                &[
                    MdocHash::new(&l).assert_valid_presentation(&given, &derived),
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
