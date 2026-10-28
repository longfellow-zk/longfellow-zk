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

use crate::compile::algebra::fp24_ext6::CompileFp24Ext6;
use crate::core::algebra::fp24::Q;
use crate::core::algebra::fp24_ext6::BETA;
use crate::core::algebra::{AlgebraicField, SerializableField, SupportsU64Conversions};
use crate::runtime::algebra::fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Subfield};
use crate::runtime::algebra::{field::RuntimeSerializableField, SubfieldV1};

#[test]
fn compile_and_runtime_fields_agree() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let a_coefficients = [Q - 1, 2, 3, 4, 5, 6];
    let b_coefficients = [7, 8, 9, 10, 11, 12];

    let mut compile_product = compile.from_coefficients(a_coefficients);
    compile.mul(
        &mut compile_product,
        &compile.from_coefficients(b_coefficients),
    );
    let mut runtime_product = runtime.from_coefficients(a_coefficients);
    runtime.mul(
        &mut runtime_product,
        &runtime.from_coefficients(b_coefficients),
    );

    assert_eq!(
        compile.to_bytes(&compile_product),
        runtime.to_bytes(&runtime_product)
    );
    // x^6 = beta in the defining quotient ring.
    let mut x = compile.from_coefficients([0, 1, 0, 0, 0, 0]);
    for _ in 1..6 {
        x = compile.mulf(&x, &compile.from_coefficients([0, 1, 0, 0, 0, 0]));
    }
    assert_eq!(x, compile.u64_to_element(u64::from(BETA)));
}

#[test]
fn inverses_and_serialization_are_canonical() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let a = compile.from_coefficients([1, 2, 3, 4, 5, 6]);
    assert_eq!(compile.mulf(&a, &compile.invert(&a)), compile.one());

    let runtime_a = runtime.from_coefficients(*a.coefficients());
    assert_eq!(
        runtime.mulf(&runtime_a, &runtime.invert(&runtime_a)),
        runtime.one()
    );
    let words = runtime.to_words64(&runtime_a);
    assert_eq!(runtime.words64_to_element(&words).unwrap(), runtime_a);

    let mut invalid = runtime.to_bytes(&runtime.zero());
    invalid[..3].copy_from_slice(&Q.to_le_bytes()[..3]);
    assert!(runtime.bytes_to_element(&invalid).is_err());

    for coefficients in [
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [Q - 1, Q - 2, 17, 29, 31, 37],
    ] {
        let value = compile.from_coefficients(coefficients);
        assert_eq!(compile.mulf(&value, &compile.invert(&value)), compile.one());
    }
}

#[test]
fn base_subfield_is_distinct_from_the_extension() {
    let runtime = RuntimeFp24Ext6::new();
    let subfield = RuntimeFp24Subfield;
    let base = runtime.u64_to_element(1234);
    let extension = runtime.from_coefficients([1234, 1, 0, 0, 0, 0]);

    assert!(subfield.contains(&base));
    assert!(!subfield.contains(&extension));
    assert_eq!(
        subfield
            .bytes_to_element(&subfield.to_bytes(&base))
            .unwrap(),
        base
    );
}

#[test]
fn compact_fp24_encodings_are_exact_and_canonical() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let subfield = RuntimeFp24Subfield;
    assert_eq!(compile.serialized_size_bytes(), 18);
    assert_eq!(runtime.serialized_size_bytes(), 18);
    assert_eq!(subfield.serialized_size_bytes(), 3);
    let coefficients = [1, 255, 256, 65_535, 65_536, Q - 1];
    let expected: Vec<_> = coefficients
        .iter()
        .flat_map(|c| c.to_le_bytes()[..3].to_vec())
        .collect();
    let value = runtime.from_coefficients(coefficients);
    assert_eq!(runtime.to_bytes(&value), expected);
    assert_eq!(
        compile.to_bytes(&compile.from_coefficients(coefficients)),
        expected
    );
    assert_eq!(runtime.bytes_to_element(&expected).unwrap(), value);
    assert_eq!(
        compile.bytes_to_element(&expected).unwrap(),
        compile.from_coefficients(coefficients)
    );
    let words = runtime.to_words64(&value);
    let word_bytes: Vec<_> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(&word_bytes[..18], expected);
    assert_eq!(&word_bytes[18..], &[0; 6]);
    assert_eq!(runtime.words64_to_element(&words).unwrap(), value);
    let mut bad_words = words;
    bad_words[2] |= 1 << 16;
    assert!(runtime.words64_to_element(&bad_words).is_err());
    for i in 0..6 {
        let mut bad = expected.clone();
        bad[3 * i..3 * i + 3].copy_from_slice(&Q.to_le_bytes()[..3]);
        assert!(runtime.bytes_to_element(&bad).is_err());
        assert!(compile.bytes_to_element(&bad).is_err());
    }
    for len in 0..=24 {
        if len != 18 {
            assert!(runtime.bytes_to_element(&vec![0; len]).is_err());
            assert!(compile.bytes_to_element(&vec![0; len]).is_err());
        }
        if len != 3 {
            assert!(subfield.bytes_to_element(&vec![0; len]).is_err());
        }
    }
    for coefficient in [0, 1, 255, 256, 65_535, 65_536, Q - 1] {
        let base_value = runtime.u64_to_element(u64::from(coefficient));
        let bytes = subfield.to_bytes(&base_value);
        assert_eq!(&bytes, &coefficient.to_le_bytes()[..3]);
        assert_eq!(subfield.bytes_to_element(&bytes).unwrap(), base_value);
    }
    assert!(subfield.bytes_to_element(&Q.to_le_bytes()[..3]).is_err());
}
