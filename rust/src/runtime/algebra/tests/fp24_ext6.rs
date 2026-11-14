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
    core::algebra::{
        AlgebraicField, Nat, SerializableField, SupportsNatConversions, SupportsU64Conversions,
    },
    runtime::algebra::{
        fp24_ext6::{RuntimeFp24Ext6, Q},
        RuntimeField, RuntimeNat,
    },
};

#[test]
fn runtime_field_laws_and_natural_reduction() {
    let f = RuntimeFp24Ext6::new();
    for i in 1..65 {
        let a = f.from_coefficients(std::array::from_fn(|j| (i * 97 + j as u32 * 131) % Q));
        let b = f.from_coefficients(std::array::from_fn(|j| (i * 31 + j as u32 * 257) % Q));
        let c = f.from_coefficients(std::array::from_fn(|j| (Q - i + j as u32) % Q));
        assert_eq!(
            f.mulf(&a, &f.addf(&b, &c)),
            f.addf(&f.mulf(&a, &b), &f.mulf(&a, &c))
        );
        assert_eq!(f.mulf(&a, &f.invert(&a)), f.one());
        assert_eq!(f.bytes_to_element(&f.to_bytes(&a)).unwrap(), a);
        let mut accum = f.zero_accum();
        f.mac(&mut accum, &a, &b);
        f.mac(&mut accum, &a, &c);
        assert_eq!(f.accum_reduce(&accum), f.mulf(&a, &f.addf(&b, &c)));
    }
    for limbs in [
        [0, 0, 0],
        [u64::from(Q), 0, 0],
        [0, 1, 0],
        [0, 0, 1],
        [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x100],
        [u64::MAX, u64::MAX, u64::MAX],
    ] {
        let n = <RuntimeNat<3> as Nat<3>>::from_limbs(&limbs);
        // Independent bitwise reduction catches limb/byte-order mistakes.
        let mut expected = 0u64;
        for bit in (0..192).rev() {
            expected = (expected * 2 + ((limbs[bit / 64] >> (bit % 64)) & 1)) % u64::from(Q);
        }
        assert_eq!(f.reduce_nat(&n), f.u64_to_element(expected));
    }
    assert_eq!(
        f.reduce_nat(&f.to_nat(&f.u64_to_element(12345))),
        f.u64_to_element(12345)
    );
}

#[test]
fn lazy_accumulator_keeps_the_full_unreduced_polynomial() {
    let f = RuntimeFp24Ext6::new();
    let high = f.from_coefficients([0, 0, 0, 0, 0, Q - 1]);
    let mut accum = f.zero_accum();
    f.mac(&mut accum, &high, &high);
    f.mac(&mut accum, &high, &high);
    assert_eq!(accum[10], 2 * u128::from(Q - 1).pow(2));
    assert!(accum[10] > u128::from(Q));
    assert!(accum[..10].iter().all(|&x| x == 0));
    assert_eq!(
        f.accum_reduce(&accum),
        f.from_coefficients([0, 0, 0, 0, 14, 0])
    );
}

#[test]
fn lazy_accumulator_matches_eager_products_and_can_be_read_repeatedly() {
    use crate::runtime::random::{DeterministicRng, RandomEngine};
    let f = RuntimeFp24Ext6::new();
    let mut rng = DeterministicRng::new(913);
    for n in [0usize, 1, 2, 3, 5, 7, 16, 257, 4096] {
        let mut accum = f.zero_accum();
        let mut expected = f.zero();
        let x = rng.elt_field_slice(n, &f);
        let y = rng.elt_field_slice(n, &f);
        for (a, b) in x.iter().zip(&y) {
            f.mac(&mut accum, a, b);
            f.fma(&mut expected, a, b);
        }
        let saved = accum;
        assert_eq!(f.accum_reduce(&accum), expected);
        assert_eq!(f.accum_reduce(&accum), expected);
        assert_eq!(accum, saved);
        assert_eq!(crate::runtime::algebra::blas::dot(&x, &y, &f), expected);
    }
}

#[test]
fn lazy_accumulator_exceeds_u64_without_losing_carries() {
    let f = RuntimeFp24Ext6::new();
    let a = f.from_coefficients([Q - 1; 6]);
    let mut accum = f.zero_accum();
    for _ in 0..65_536 {
        f.mac(&mut accum, &a, &a);
    }
    assert!(accum[5] > u128::from(u64::MAX));
    assert_eq!(
        f.accum_reduce(&accum),
        f.mulf(&f.mulf(&a, &a), &f.u64_to_element(65_536))
    );
}

#[test]
fn lazy_accumulator_handles_the_u64_batch_length_bound() {
    let f = RuntimeFp24Ext6::new();
    let n = u128::from(u64::MAX);
    let product = u128::from(Q - 1).pow(2);
    let accum = std::array::from_fn(|degree| {
        let terms = if degree < 6 { degree + 1 } else { 11 - degree };
        terms as u128 * n * product
    });
    assert!(accum.iter().any(|&x| x > u128::from(u64::MAX)));
    assert!(36 * n * product < (1u128 << 116));
    let a = f.from_coefficients([Q - 1; 6]);
    let scalar = f.u64_to_element((n % u128::from(Q)) as u64);
    assert_eq!(f.accum_reduce(&accum), f.mulf(&f.mulf(&a, &a), &scalar));
}
