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

use circuits_experimental::mldsa::{algebra::RuntimeFp24Ext6, crt::CrtReedSolomonFactory};
use core_algebra::AlgebraicField;
use runtime_algebra::{Interpolator, InterpolatorFactory};

#[test]
fn crt_interpolation_encodes_all_six_coefficients() {
    let field = RuntimeFp24Ext6::new();
    let polynomial: Vec<_> = (0..7)
        .map(|i| field.from_coefficients(std::array::from_fn(|j| (13 * i + 7 * j + 1) as u32)))
        .collect();
    let evaluate = |point: usize| {
        polynomial
            .iter()
            .rev()
            .fold(field.zero(), |accumulator, coefficient| {
                field.addf(
                    &field.mulf(
                        &accumulator,
                        &field.from_coefficients([point as u32, 0, 0, 0, 0, 0]),
                    ),
                    coefficient,
                )
            })
    };
    let mut evaluations: Vec<_> = (0..16).map(evaluate).collect();
    let expected = evaluations.clone();
    evaluations[7..].fill(field.zero());

    let factory = CrtReedSolomonFactory;
    assert!(factory.can_encode(7, 16));
    factory.make(7, 16).interpolate(&mut evaluations);
    assert_eq!(evaluations, expected);
}
