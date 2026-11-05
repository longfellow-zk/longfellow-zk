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
    circuits::{analog_decoder::AnalogDecoder, boolean::Boolean},
    compile::{
        algebra::{
            field::{CompileField, SupportsNatConversions, SupportsU64Conversions},
            p256::P256Field,
        },
        logic::{eval::EvalLogic, Logic, LogicIO},
    },
};

#[test]
fn test_compile_analog_decoder() {
    let f = P256Field::new();
    let (circuit, stats, _symbols) = compile(&f, |iologic| {
        let ad = AnalogDecoder::new(&iologic);

        let n = 5;
        let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let x = iologic.next(&mut pos);

        let decoder = ad.unary(n);
        let (exactly_one, _decoded) = decoder.decode(&x);
        (exactly_one, 1, 0)
    });
    crate::compile::compiler::dump_stats("analog_decoder_compile", &circuit, &stats);
}

#[test]
fn test_compile_analog_decoder_binary() {
    let f = P256Field::new();
    let (circuit, stats, _symbols) = compile(&f, |iologic| {
        let ad = AnalogDecoder::new(&iologic);
        let boolean = Boolean::new(&iologic);

        let width = 3;
        let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let x = iologic.next(&mut pos);

        let decoder = ad.binary(width);
        let decoded = decoder.decode(&x);

        (boolean.assert_true("assert_decoded0", &decoded[0]), 1, 0)
    });

    crate::compile::compiler::dump_stats("analog_decoder_binary_compile", &circuit, &stats);
}

fn test_analog_decoder_unary_generic<
    const W: usize,
    F: CompileField + SupportsNatConversions<W>,
>(
    f: &F,
) {
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let iologic = EvalLogic::new(f, &tracker);
    let ad = AnalogDecoder::new(&iologic);
    let boolean = Boolean::new(&iologic);

    let n = 15;
    let decoder = ad.unary(n);

    for i in 0..n {
        let pt = ad.unary_point(n, i);
        let pt_wire = iologic.konst(&pt);
        let (assertion, decoded) = decoder.decode(&pt_wire);
        assert!(
            assertion.is_ok(),
            "Assertion failed for valid point i = {i}"
        );

        assert_eq!(decoded.len(), n);
        for (k, dec_wire) in decoded.iter().enumerate() {
            let want = i == k;
            let got_elt = boolean.as_eltw(dec_wire);
            let want_val = if want { f.one() } else { f.zero() };
            assert_eq!(
                want_val, got_elt.value,
                "Mismatch at input i = {i}, check index k = {k}"
            );
        }
    }

    // Test invalid point
    let invalid_pt = f.addf(&ad.unary_point(n, 0), &f.one());
    let invalid_pt_wire = iologic.konst(&invalid_pt);
    let (assertion, _decoded) = decoder.decode(&invalid_pt_wire);
    assert!(assertion.is_err(), "Assertion succeeded for invalid point!");
}

fn test_analog_decoder_binary_generic<
    const W: usize,
    F: CompileField + SupportsNatConversions<W>,
>(
    f: &F,
) {
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let iologic = EvalLogic::new(f, &tracker);
    let ad = AnalogDecoder::new(&iologic);
    let boolean = Boolean::new(&iologic);

    let width = 4;
    let n = 1 << width;
    let decoder = ad.binary(width);

    for i in 0..n {
        let pt = ad.binary_point(width, i);
        let pt_wire = iologic.konst(&pt);
        let got = decoder.decode(&pt_wire);

        assert_eq!(got.len(), width);
        for (k, got_wire) in got.iter().enumerate() {
            let want = ((i >> k) & 1) == 1;
            let got_elt = boolean.as_eltw(got_wire);
            let want_val = if want { f.one() } else { f.zero() };
            assert_eq!(
                want_val, got_elt.value,
                "Mismatch at input i = {i}, check bit index k = {k}"
            );
        }
    }
}

struct F1009Tag;
type F1009Field = crate::compile::algebra::fp::FpField<F1009Tag>;

fn new_f1009_field() -> F1009Field {
    crate::compile::algebra::fp::FpField::new_field(crate::compile::algebra::fp::FpParameters {
        length_bytes: 2,
        modulo: crate::compile::algebra::CompileNat::<4>::from(1009),
    })
}

fn test_analog_decoder_exhaustive_field_1009_generic<
    const W: usize,
    F: CompileField + SupportsNatConversions<W> + SupportsU64Conversions,
>(
    f: &F,
) {
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let iologic = EvalLogic::new(f, &tracker);
    let ad = AnalogDecoder::new(&iologic);
    let boolean = Boolean::new(&iologic);

    // Test all unary lengths from 2 up to 10
    for n in 2..=10 {
        let decoder = ad.unary(n);

        // Collect all valid points for this unary decoder
        let mut valid_points = Vec::with_capacity(n);
        for i in 0..n {
            valid_points.push(ad.unary_point(n, i));
        }

        // Exhaustively check all 1009 possible elements in the field.
        for val in 0..1009 {
            let pt = f.u64_to_element((val) as u64);
            let pt_wire = iologic.konst(&pt);
            let (assertion, decoded) = decoder.decode(&pt_wire);

            if let Some(i) = valid_points.iter().position(|vp| vp == &pt) {
                // It is a valid point: assertion must succeed
                assert!(
                    assertion.is_ok(),
                    "Unary(n={n}) assertion failed for valid point val = {val} (index {i})"
                );
                // Result must be one-hot with 1 at index i
                for (k, dec_wire) in decoded.iter().enumerate() {
                    let got_elt = boolean.as_eltw(dec_wire);
                    let want_val = if k == i { f.one() } else { f.zero() };
                    assert_eq!(
                        want_val, got_elt.value,
                        "Unary(n={n}) value mismatch for valid point val = {val}, check index {k}"
                    );
                }
            } else {
                // It is an invalid point: assertion must fail
                assert!(
                    assertion.is_err(),
                    "Unary(n={n}) assertion succeeded for invalid point val = {val}"
                );
            }
        }
    }

    // Test all binary widths up to 5
    for width in 1..=5 {
        let n = 1 << width;
        let decoder = ad.binary(width);

        // Collect all valid points for this binary decoder
        let mut valid_points = Vec::with_capacity(n);
        for i in 0..n {
            valid_points.push(ad.binary_point(width, i));
        }

        // Exhaustively check all 1009 possible elements in the field.
        for val in 0..1009 {
            let pt = f.u64_to_element((val) as u64);
            let pt_wire = iologic.konst(&pt);
            let got = decoder.decode(&pt_wire);

            // Collect internal bit assertions for the decoded bits
            let is_ok = got.iter().all(|bit| {
                boolean
                    .as_eltw(bit)
                    .assertions
                    .values()
                    .all(|s| matches!(s, crate::compile::logic::scope::AssertionStatus::Passed))
            });

            if let Some(i) = valid_points.iter().position(|vp| vp == &pt) {
                // It is a valid point: bit assertions must succeed
                assert!(
                    is_ok,
                    "Binary(w={width}) assertions failed for valid point val = {val} (index {i})"
                );
                // Result must match bit representation of index i
                assert_eq!(got.len(), width);
                for (k, got_wire) in got.iter().enumerate() {
                    let want = ((i >> k) & 1) == 1;
                    let got_elt = boolean.as_eltw(got_wire);
                    let want_val = if want { f.one() } else { f.zero() };
                    assert_eq!(
                        want_val, got_elt.value,
                        "Binary(w={width}) value mismatch at valid point val = {val}, bit index {k}"
                    );
                }
            } else {
                // It is an invalid point: at least one bit assertion must fail
                // (since the values will not be 0 or 1)
                assert!(
                    !is_ok,
                    "Binary(w={width}) assertions succeeded for invalid point val = {val}"
                );
            }
        }
    }
}

#[test]
fn test_analog_decoder_exhaustive_field_1009() {
    let f = new_f1009_field();
    test_analog_decoder_exhaustive_field_1009_generic::<4, _>(&f);
}

#[test]
fn test_analog_decoder_evaluation() {
    let f = P256Field::new();
    test_analog_decoder_unary_generic::<4, _>(&f);
    test_analog_decoder_binary_generic::<4, _>(&f);
}

#[test]
fn binary_field_decoders_retain_range_assertions_on_derived_values() {
    use crate::{
        compile::{algebra::gf2_128::Gf2_128Field, logic::scope::AssertionStatus},
        core::algebra::{AlgebraicField, SupportsU128Conversions},
    };
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let decoder = AnalogDecoder::new(&logic);
    let boolean = Boolean::new(&logic);
    let binary = decoder.binary(3);
    let valid_points: Vec<_> = (0..8).map(|i| decoder.binary_point(3, i)).collect();
    for (i, value) in valid_points.iter().enumerate() {
        let bits = binary.decode(&logic.konst(value));
        for (k, bit) in bits.iter().enumerate() {
            let wire = boolean.as_eltw(bit);
            assert_eq!(wire.value, if i >> k & 1 == 1 { f.one() } else { f.zero() });
            assert!(!wire.assertions.is_empty());
            assert!(wire
                .assertions
                .values()
                .all(|s| matches!(s, AssertionStatus::Passed)));
        }
    }
    // These are full-field intermediate values, not Boolean circuit inputs.
    // Every returned bit must carry the failed range check, regardless of its value.
    for value in [decoder.binary_point(3, 8), f.u128_to_element(1 << 100)] {
        assert!(!valid_points.contains(&value));
        for bit in binary.decode(&logic.konst(&value)) {
            assert!(boolean
                .as_eltw(&bit)
                .assertions
                .values()
                .any(|s| matches!(s, AssertionStatus::Failed(_))));
        }
    }
    let unary = decoder.unary(5);
    let (assertion, bits) = unary.decode(&logic.konst(&decoder.unary_point(5, 5)));
    assert!(assertion.is_err());
    for bit in bits {
        assert!(boolean
            .as_eltw(&bit)
            .assertions
            .values()
            .any(|s| matches!(s, AssertionStatus::Failed(_))));
    }

    // A one-bit table has a nonconstant affine interpolant. An input outside
    // its two points therefore produces a nonbit, which the standalone API
    // must reject even without a shared input-range assertion.
    let standalone = decoder.bit(1, 0);
    let outside = logic.konst(&decoder.binary_point(1, 2));
    let result = boolean.as_eltw(&standalone.decode(&outside));
    assert_ne!(result.value, f.zero());
    assert_ne!(result.value, f.one());
    assert!(result
        .assertions
        .values()
        .any(|s| matches!(s, AssertionStatus::Failed(_))));
}
