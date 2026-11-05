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
        AlgebraicField, SerializableField, SupportsU128Conversions, SupportsU64Conversions,
    },
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
            cross: f.zero(),
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
            cross: f.zero(),
            claims: [f.zero(), f.zero()],
        }],
    };
    for z in [f.zero(), f.one(), f.mone(), element(7)] {
        let expected = f.addf(&c0, &f.mulf(&z, &f.addf(&c1, &f.mulf(&z, &c2))));
        let layer_challenges = vec![LayerChallenges {
            terminal: f.one(),
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

#[test]
fn round_polynomial_and_constraints_extension() {
    let f = crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new();
    let element = |x: u64| f.from_coefficients([x as u32, 1, 2, 3, 4, 5]);
    check_round_polynomial(&f, element);
    check_round_constraints(&f, element);
}

// A dishonest product cell is allowed. Construct an error polynomial with two
// chosen roots, and check the actual symbolic terminal against that polynomial.
// This catches signs and challenge powers in both characteristics, and shows why
// the soundness cost is two roots rather than an unchecked multiplication.
fn check_terminal<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    use crate::runtime::sumcheck_v2::symbolic::Pad;
    let a = element(7);
    let b = element(11);
    let pa = element(13);
    let pb = element(17);
    let pd = element(19);
    let r1 = element(2);
    let r2 = element(5);
    let error = element(3);
    let c2 = f.mulf(&error, &f.invert(&f.mulf(&r1, &r2)));
    let c1 = f.neg(&f.mulf(&c2, &f.addf(&r1, &r2)));
    for dishonest in [false, true] {
        let mut claim = f.mulf(&a, &b);
        let mut product = f.mulf(&pa, &pb);
        let mut cross = f.subf(&f.addf(&f.mulf(&a, &pb), &f.mulf(&b, &pa)), &pd);
        if dishonest {
            f.add(&mut claim, &error);
            f.add(&mut product, &c2);
            f.add(&mut cross, &c1);
        }
        let mut roots = 0;
        for value in 1..64 {
            let r = element(value);
            let proof = SumcheckProof::<W, F> {
                layers: vec![LayerProof {
                    rounds: vec![],
                    cross: cross.clone(),
                    claims: [f.addf(&a, &f.mulf(&r, &pa)), f.addf(&b, &f.mulf(&r, &pb))],
                }],
            };
            let constraints = build_constraints(
                &proof,
                vec![LayerChallenges {
                    // With no rounds, -K supplies the incoming terminal claim.
                    constant: f.neg(&claim),
                    linear: f.zero(),
                    point_l: vec![],
                    terminal: r.clone(),
                    alpha: element(23),
                }],
                vec![],
                f,
            );
            let evaluate =
                |expression: &crate::runtime::sumcheck_v2::symbolic::PadExpression<F::E>| {
                    let mut value = expression.constant.clone();
                    for (pad, coefficient) in &expression.terms {
                        let cell = match pad {
                            Pad::Claim { slot: 0, .. } => &pa,
                            Pad::Claim { slot: 1, .. } => &pb,
                            Pad::Product { .. } => &product,
                            Pad::Cross { .. } => &pd,
                            _ => panic!("unexpected pad in a zero-round terminal"),
                        };
                        f.fma(&mut value, coefficient, cell);
                    }
                    value
                };
            let residual = evaluate(&constraints.layers[0]);
            let expected = if dishonest {
                f.mulf(&c2, &f.mulf(&f.subf(&r, &r1), &f.subf(&r, &r2)))
            } else {
                f.zero()
            };
            assert_eq!(residual, expected);
            roots += usize::from(f.is_zero(&residual));
            assert_eq!(
                evaluate(&constraints.input_claim),
                f.addf(&a, &f.mulf(&element(23), &b))
            );
        }
        assert_eq!(roots, if dishonest { 2 } else { 63 });
    }
}

#[test]
fn terminal_honesty_and_forged_product_roots() {
    let prime = P256Field::new();
    check_terminal(&prime, |x| prime.u64_to_element(x));
    let binary = Gf2_128Field::new();
    check_terminal(&binary, |x| binary.u128_to_element(x as u128));
}

#[test]
fn terminal_transcript_fixes_cross_before_scale_and_claims_before_combination() {
    use crate::runtime::{
        random::{RandomEngine, Transcript},
        sumcheck_v2::transcript,
    };
    let f = P256Field::new();
    let cross = f.u64_to_element(13);
    let mut prover = Transcript::new(b"terminal-order");
    let mut reference = prover.clone();
    reference.write_bytes(b"single-hand-linear-terminal/v1");
    reference.write_elt_field(&cross, &f);
    let expected = reference.elt_field(&f);
    assert_ne!(expected, f.zero());
    let r = transcript::terminal_challenge(&cross, &mut prover, &f);
    assert_eq!(r, expected);
    assert_eq!(prover.clone().bytes(32), reference.clone().bytes(32));

    let claims = [f.u64_to_element(17), f.u64_to_element(19)];
    let mut changed = prover.clone();
    reference.write_elt_field_slice(&claims, &f);
    reference.write_bytes(b"single-hand-combine");
    let alpha = transcript::end_layer::<4, _>(&claims, &mut prover, &f);
    assert_eq!(alpha, reference.elt_field(&f));
    assert_eq!(prover.bytes(32), reference.bytes(32));
    let changed_alpha = transcript::end_layer::<4, _>(&[claims[1], claims[0]], &mut changed, &f);
    assert_ne!(alpha, changed_alpha);
    let mut changed_cross = Transcript::new(b"terminal-order");
    assert_ne!(
        r,
        transcript::terminal_challenge(&f.one(), &mut changed_cross, &f)
    );
}
