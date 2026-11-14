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

//! Generic runtime field operations, checked independently of protocol code.
use crate::{
    core::algebra::{SerializableField, SupportsU128Conversions},
    runtime::algebra::{AlgebraicField, RuntimeField},
};

fn check_constant_encoding<F: AlgebraicField + SerializableField>(field: &F) {
    let width = field.serialized_size_bytes();
    assert!(width > 0);
    let zero = vec![0; width];
    let mut one = zero.clone();
    one[0] = 1;
    for (value, bytes) in [
        (field.zero(), zero),
        (field.one(), one),
        (field.mone(), field.serialized_mone()),
    ] {
        assert_eq!(bytes.len(), width);
        assert_eq!(field.to_bytes(&value), bytes);
        assert_eq!(field.bytes_to_element(&bytes).unwrap(), value);
    }
    use crate::core::proto::v2::{classify_constants, CoefficientClass};
    let minus_class = if field.mone() == field.one() {
        CoefficientClass::One
    } else {
        CoefficientClass::MinusOne
    };
    assert_eq!(
        classify_constants(field, &[field.zero(), field.one(), field.mone()]),
        [CoefficientClass::Zero, CoefficientClass::One, minus_class]
    );
}

#[test]
fn serializable_fields_use_canonical_constant_encodings() {
    use crate::{compile::algebra as compile, runtime::algebra as runtime};
    check_constant_encoding(&crate::core::algebra::gf2_128::Gf2_128Field::new());
    check_constant_encoding(&compile::gf2_128::Gf2_128Field::new());
    check_constant_encoding(&compile::p256::P256Field::new());
    check_constant_encoding(&compile::q256::Q256Field::new());
    check_constant_encoding(&compile::fp24_ext6::CompileFp24Ext6::new());
    check_constant_encoding(&runtime::gf2_128::Gf2_128Field::new());
    check_constant_encoding(&runtime::p256::P256Field::new());
    check_constant_encoding(&runtime::q256::Q256Field::new());
    check_constant_encoding(&runtime::fp24_ext6::RuntimeFp24Ext6::new());
    check_constant_encoding(&runtime::packing::binary::Gf2);
    check_constant_encoding(&runtime::packing::binary::Gf256::new());
    check_constant_encoding(&runtime::packing::prime24::Prime24);
}

fn check<const W: usize, F: RuntimeField<W>>(field: &F, value: F::E) {
    let mut expected = field.one();
    for exponent in 0..64 {
        assert_eq!(field.pow(&value, exponent), expected);
        field.mul(&mut expected, &value);
    }
    assert_eq!(field.pow(&field.zero(), 0), field.one());
    assert_eq!(field.pow(&field.zero(), usize::MAX), field.zero());
    assert_eq!(field.pow(&field.one(), usize::MAX), field.one());
    assert_eq!(field.pow(&field.mone(), usize::MAX), field.mone());
}

#[test]
fn power_works_in_binary_prime_and_extension_fields() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, gf2_128::Gf2_128Field, p256::P256Field, q256::Q256Field,
    };
    let binary = Gf2_128Field::new();
    check(&binary, binary.u128_to_element(3));
    let prime = P256Field::new();
    check(&prime, prime.addf(&prime.one(), &prime.one()));
    let scalar = Q256Field::new();
    check(&scalar, scalar.addf(&scalar.one(), &scalar.one()));
    let extension = Fp2Field::new(&prime);
    check(
        &extension,
        extension.addf(&extension.one(), &extension.one()),
    );
    {
        let sextic = crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new();
        check(&sextic, sextic.addf(&sextic.one(), &sextic.one()));
    }
}
