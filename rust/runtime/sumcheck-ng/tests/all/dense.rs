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

use runtime_algebra::{field::SupportsU64Conversions, p256::P256Field};
use runtime_sumcheck_ng::{as_scalar, bind};

fn check_binding<const W: usize, F: runtime_algebra::RuntimeField<W>>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    for n in [1usize, 2, 3, 7, 8] {
        let logn = n.next_power_of_two().ilog2() as usize;
        let point: Vec<_> = (0..logn).map(|i| element(7 + i as u64)).collect();
        let mut values: Vec<_> = (0..n).map(|i| element(3 + i as u64)).collect();
        let weights = runtime_sumcheck_ng::eq::weights(logn, n, &point, f);
        let expected = runtime_algebra::blas::dot(&weights, &values, f);
        for challenge in point {
            bind(&mut values, &challenge, f);
        }
        assert_eq!(as_scalar::<W, F>(&values), expected);
    }
}

#[test]
fn binding_matches_equality_weights_prime() {
    let f = P256Field::new();
    check_binding(&f, |x| f.u64_to_element(x));
}

#[test]
fn binding_matches_equality_weights_binary() {
    use core_algebra::SupportsU128Conversions;
    let f = runtime_algebra::gf2_128::Gf2_128Field::new();
    check_binding(&f, |x| f.u128_to_element(x as u128));
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
