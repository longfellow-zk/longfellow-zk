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

use crate::runtime::{
    algebra::{field::SupportsU64Conversions, p256::P256Field},
    v2::sumcheck::{bind, dense::as_scalar},
};

fn check_binding<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    for n in [1usize, 2, 3, 7, 8, 13, 16] {
        // Extra variables exercise implicit zero high coefficients and repeated
        // binding of a scalar, both of which must preserve the constant term.
        for extra in [0, 2] {
            let logn = n.next_power_of_two().ilog2() as usize + extra;
            for seed in [0, 1, 7] {
                let point: Vec<_> = (0..logn)
                    .map(|j| element(if seed < 2 { seed } else { seed + j as u64 }))
                    .collect();
                let mut values: Vec<_> = (0..n).map(|i| element(3 + i as u64)).collect();
                let weights = crate::runtime::v2::sumcheck::monomial::weights(logn, n, &point, f);
                let mut expected = f.zero();
                for i in 0..n {
                    let mut weight = f.one();
                    for (j, z) in point.iter().enumerate() {
                        if (i >> j) & 1 != 0 {
                            f.mul(&mut weight, z);
                        }
                    }
                    assert_eq!(weights[i], weight);
                    f.fma(&mut expected, &weight, &values[i]);
                }
                for z in point {
                    bind(&mut values, &z, f);
                }
                assert_eq!(as_scalar::<W, F>(&values), expected);
            }
        }
    }
    assert!(crate::runtime::v2::sumcheck::monomial::weights(0, 0, &[], f).is_empty());
}

#[test]
fn binding_matches_monomial_weights_prime() {
    let f = P256Field::new();
    check_binding(&f, |x| f.u64_to_element(x));
}

#[test]
fn binding_matches_monomial_weights_binary() {
    use crate::core::algebra::SupportsU128Conversions;
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    check_binding(&f, |x| f.u128_to_element(x as u128));
}

#[test]
fn binding_matches_monomial_weights_extension() {
    let f = crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new();
    check_binding(&f, |x| {
        if x < 2 {
            f.u64_to_element(x)
        } else {
            f.from_coefficients([x as u32, 1, 2, 3, 4, 5])
        }
    });
}

#[test]
fn test_as_scalar() {
    let f = P256Field::new();
    let vec_one = vec![f.u64_to_element(42)];
    assert_eq!(as_scalar::<4, P256Field>(&vec_one), f.u64_to_element(42));
}

#[test]
#[should_panic(expected = "vector length must be 1")]
fn test_as_scalar_panic() {
    let f = P256Field::new();
    let vec_two = vec![f.u64_to_element(1), f.u64_to_element(2)];
    as_scalar::<4, P256Field>(&vec_two);
}
