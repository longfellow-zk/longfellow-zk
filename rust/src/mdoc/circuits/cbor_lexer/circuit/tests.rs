// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CborLexer, Counter, Header, Witness};
use crate::{
    circuits::{bitvec::BitvecLogic, boolean::Boolean},
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, CompileField},
        logic::{AssertionScope, EvalLogic, Logic},
    },
    core::algebra::SupportsU128Conversions,
};

fn check_header<F: CompileField>(field: &F) {
    let scope = AssertionScope::new();
    let logic = EvalLogic::new(field, &scope);
    let bv = BitvecLogic::new(&logic);
    let boolean = Boolean::new(&logic);
    for byte in 0..=u8::MAX {
        let header = Header::decode(&bv, &boolean, &bv.of_u8(byte));
        let major = byte >> 5;
        let info = byte & 31;
        for (actual, expected) in [
            (&header.stringp, matches!(major, 2 | 3)),
            (&header.itemsp, matches!(major, 4 | 5)),
            (&header.mapp, major == 5),
            (&header.arrayp, major == 4),
            (&header.tagp, major == 6),
            (&header.specialp, major == 7),
            (&header.simple_specialp, byte & 0xfc == 0xf4),
            (&header.count0_23, info < 24),
            (&header.count24_27, (24..28).contains(&info)),
            (&header.count24, info == 24),
            (&header.count25, info == 25),
        ] {
            assert_eq!(
                boolean.as_eltw(actual),
                logic.konst(&if expected { field.one() } else { field.zero() }),
                "header {byte:02x}"
            );
        }
    }
}
fn check_arguments<F: CompileField + SupportsU128Conversions>(field: &F) {
    let scope = AssertionScope::new();
    let logic = EvalLogic::new(field, &scope);
    let bv = BitvecLogic::new(&logic);
    let counter = Counter::new(&logic, 16);
    let low = (0..256)
        .map(|n| counter.encode(&bv.of_u64::<16>(n)))
        .collect::<Vec<_>>();
    let high = (0..256)
        .map(|n| counter.encode(&bv.of_u64::<16>(n << 8)))
        .collect::<Vec<_>>();
    for n in 0..=u16::MAX {
        let expected = if field.is_binary() {
            let mut power = field.pseudo_basis(1);
            let mut value = field.one();
            let mut exponent = n;
            while exponent != 0 {
                if exponent & 1 != 0 {
                    field.mul(&mut value, &power);
                }
                power = field.mulf(&power, &power);
                exponent >>= 1;
            }
            value
        } else {
            field.u128_to_element(u128::from(n))
        };
        assert_eq!(
            counter.add(&high[usize::from(n >> 8)], &low[usize::from(n & 255)]),
            logic.konst(&expected),
            "argument {n}"
        );
    }
}
#[test]
fn header_flags_match_all_256_byte_values() {
    check_header(&Gf2_128Field::new());
    check_header(&P256Field::new());
}
#[test]
fn byte_encoded_arguments_match_all_65536_integer_values() {
    check_arguments(&Gf2_128Field::new());
    check_arguments(&P256Field::new());
}

#[test]
fn bounded_lengths_reject_integer_wraparound_in_a_small_prime_field() {
    use crate::{
        compile::algebra::{
            fp::{FpField, FpParameters},
            CompileNat,
        },
        core::algebra::Nat,
    };
    struct Prime97;
    let field = FpField::<Prime97>::new_field(FpParameters {
        length_bytes: 1,
        modulo: CompileNat::<1>::from_u64(97),
    });
    // 97 is zero in this field. A forged three-byte countdown would match
    // a 97-byte payload if the argument's *integer* capacity check were lost.
    for (header, valid) in [(0x19, true), (0x59, false), (0x99, false), (0xb9, false)] {
        let scope = AssertionScope::new();
        let logic = EvalLogic::new(&field, &scope);
        let bv = BitvecLogic::new(&logic);
        let mut bytes = vec![bv.of_u8(0); 16];
        bytes[..3].clone_from_slice(&[bv.of_u8(header), bv.of_u8(0), bv.of_u8(97)]);
        let mut remaining = vec![0; 16];
        remaining[..3].copy_from_slice(&[2, 1, 0]);
        let lexed = CborLexer::new(&logic).lex(
            &bytes,
            &bv.of_u64::<5>(3),
            &Witness::constant(&logic, &remaining),
        );
        assert_eq!(lexed.assertions().is_ok(), valid, "header {header:02x}");
    }
}
