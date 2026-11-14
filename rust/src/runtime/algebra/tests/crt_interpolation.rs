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
    core::algebra::AlgebraicField,
    runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory, InterpolationPlan,
        RangeInterpolatorFactory,
    },
};

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
    let expected: Vec<_> = (0..16).map(evaluate).collect();

    let factory = CrtInterpolatorFactory;
    assert!(factory.can_interpolate(0..7, 7..16));
    let actual = factory.make_range(0..7, 7..16).apply(&expected[..7]);
    assert_eq!(actual, expected[7..]);
}

#[test]
fn interpolation_matches_direct_evaluation_at_domain_boundaries() {
    let f = RuntimeFp24Ext6::new();
    for n in [1usize, 2, 3, 8, 17] {
        for m in [n, n + 1, 2 * n + 3] {
            let coefficients: Vec<_> = (0..n)
                .map(|i| {
                    f.from_coefficients(std::array::from_fn(|j| {
                        ((i * 131 + j * 17 + 1) % (crate::core::algebra::fp24::Q as usize)) as u32
                    }))
                })
                .collect();
            let mut expected = Vec::new();
            for point in 0..m {
                let x = f.from_coefficients([point as u32, 0, 0, 0, 0, 0]);
                expected.push(
                    coefficients
                        .iter()
                        .rev()
                        .fold(f.zero(), |a, b| f.addf(&f.mulf(&a, &x), b)),
                );
            }
            assert!(CrtInterpolatorFactory.can_interpolate(0..n, n..m));
            let actual = CrtInterpolatorFactory
                .make_range(0..n, n..m)
                .apply(&expected[..n]);
            assert_eq!(actual, expected[n..], "n={n}, m={m}");
        }
    }
}

#[test]
fn interpolation_rejects_unsupported_geometries() {
    let factory = CrtInterpolatorFactory;
    let q = crate::core::algebra::fp24::Q as usize;
    for (source, destination) in [
        (0..0, 0..1),
        (0..1, 1..usize::MAX),
        (0..2, q..q + 1),
        (0..1 << 22, 1 << 22..(1 << 22) + 1),
    ] {
        assert!(!factory.can_interpolate(source, destination));
    }
    let maximal = u128::from(crate::core::algebra::fp24::Q - 1);
    let limit = ((18_446_744_072_195_407_873u128 - 1) / (maximal * maximal)) as usize;
    assert!(factory.can_interpolate(0..limit, limit..limit + 1));
    assert!(!factory.can_interpolate(0..limit + 1, limit + 1..limit + 2));
    // Copies and constants require no convolution and are not limited by FFT size.
    assert!(factory.can_interpolate(0..limit + 1, 0..limit + 1));
    assert!(factory.can_interpolate(0..1, (1 << 22)..(1 << 22) + 1));
}
