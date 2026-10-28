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
    core::algebra::{SerializableField, SupportsU128Conversions, SupportsU64Conversions},
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field, p256::P256Field, RuntimeField},
        sumcheck_v2::{
            prover::quad_round_poly, symbolic::build_constraints, LayerChallenges, LayerProof,
            RoundPoly, SumcheckProof,
        },
    },
};

// Compare the optimized two-product kernel with all three coefficients expanded
// directly, then evaluate at finite challenges and compare with bound input pairs.
fn check_round_polynomial<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    for n in [1usize, 2, 3, 7, 8, 13, 16] {
        let q_l: Vec<_> = (0..n).map(|i| element(3 + i as u64)).collect();
        let w: Vec<_> = (0..n).map(|i| element(11 + 2 * i as u64)).collect();
        let claim = blas::dot(&q_l, &w, f);
        let p = quad_round_poly(&q_l, &w, &claim, f);
        let mut c0 = f.zero();
        let mut c1 = f.zero();
        let mut c2 = f.zero();
        for i in (0..n).step_by(2) {
            f.fma(&mut c0, &q_l[i], &w[i]);
            if i + 1 < n {
                f.fma(&mut c1, &q_l[i], &w[i + 1]);
                f.fma(&mut c1, &q_l[i + 1], &w[i]);
                f.fma(&mut c2, &q_l[i + 1], &w[i + 1]);
            }
        }
        assert_eq!(p.coefficients, [c0.clone(), c1.clone()]);
        assert_eq!(claim, f.addf(&c0, &c2));
        for z in [f.zero(), f.one(), f.mone(), element(7)] {
            let mut expected = f.zero();
            for i in (0..n).step_by(2) {
                let mut q = q_l[i].clone();
                let mut value = w[i].clone();
                if i + 1 < n {
                    f.fma(&mut q, &z, &q_l[i + 1]);
                    f.fma(&mut value, &z, &w[i + 1]);
                }
                f.fma(&mut expected, &q, &value);
            }
            let actual = f.addf(&c0, &f.mulf(&z, &f.addf(&c1, &f.mulf(&z, &c2))));
            assert_eq!(actual, expected);
        }
    }
}

#[test]
fn round_polynomial_matches_bound_product_prime() {
    let f = P256Field::new();
    check_round_polynomial(&f, |x| f.u64_to_element(x));
}

#[test]
fn round_polynomial_matches_bound_product_binary() {
    let f = Gf2_128Field::new();
    check_round_polynomial(&f, |x| f.u128_to_element(x as u128));
}

// Check the symbolic round at 0, 1, -1, and an ordinary challenge, including
// vanished old/new pad coefficients. The incoming claim is zero, so c2 = -c0.
fn check_round_constraints<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    let c0 = element(3);
    let c1 = element(14);
    let c2 = f.neg(&c0);
    let pads = SumcheckProof::<W, F> {
        layers: vec![LayerProof {
            rounds: vec![RoundPoly {
                coefficients: [element(5), element(9)],
            }],
            claims: [f.zero(), f.zero()],
        }],
    };
    let proof = SumcheckProof::<W, F> {
        layers: vec![LayerProof {
            rounds: vec![RoundPoly {
                coefficients: [
                    f.subf(&c0, &pads.layers[0].rounds[0].coefficients[0]),
                    f.subf(&c1, &pads.layers[0].rounds[0].coefficients[1]),
                ],
            }],
            claims: [f.zero(), f.zero()],
        }],
    };
    for z in [f.zero(), f.one(), f.mone(), element(7)] {
        let expected = f.addf(&c0, &f.mulf(&z, &f.addf(&c1, &f.mulf(&z, &c2))));
        let layer_challenges = vec![LayerChallenges {
            constant: f.zero(),
            linear: f.zero(),
            point_l: vec![z],
            alpha: f.one(),
        }];
        let constraints = build_constraints(&proof, layer_challenges, vec![], f);
        // A = B = 0, so the layer residual is p(z) and the input residual is zero.
        assert_eq!(
            constraints.residuals(&[], &pads, f).unwrap(),
            vec![expected, f.zero()]
        );
    }
}

#[test]
fn round_constraints_match_polynomial_prime() {
    let f = P256Field::new();
    check_round_constraints(&f, |x| f.u64_to_element(x));
}

#[test]
fn round_constraints_match_polynomial_binary() {
    let f = Gf2_128Field::new();
    check_round_constraints(&f, |x| f.u128_to_element(x as u128));
}

#[cfg(feature = "experimental")]
#[test]
fn round_polynomial_and_constraints_extension() {
    let f = crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new();
    let element = |x: u64| f.from_coefficients([x as u32, 1, 2, 3, 4, 5]);
    check_round_polynomial(&f, element);
    check_round_constraints(&f, element);
}
