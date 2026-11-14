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
    core::algebra::SupportsU64Conversions,
    runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, InterpolationPlan,
        RangeInterpolatorFactory, SupportsFFT,
    },
};

#[test]
fn integer_domain_polynomial_regression() {
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let domain =
        QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    let source: Vec<_> = [1, 2, 5, 10, 17].map(|v| f.u64_to_element(v)).into();
    let actual = domain.make_range(0..5, 5..10).apply(&source);
    assert_eq!(actual, [26, 37, 50, 65, 82].map(|v| f.u64_to_element(v)));
}
