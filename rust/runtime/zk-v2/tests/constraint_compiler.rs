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

use crate::runtime::algebra::{blas, ElementOf};
/// Emit one equation per circuit layer and one final input equation, in that order.
/// Preserve all terms, including zero coefficients; repeated terms remain additive.
/// Equations and their constants remain even when every variable coefficient vanishes.
fn compile_direct<const W: usize, F: RuntimeField<W>>(
    constraints: &Constraints<ElementOf<F>>,
    pads: &CircuitPadLayout,
    public_inputs: &[ElementOf<F>],
    f: &F,
) -> Result<(Vec<PolygeroLinearTerm<ElementOf<F>>>, Vec<ElementOf<F>>), String> {
    validate(constraints, pads, public_inputs.len())?;
    let (mut a, mut b) = compile_layers(constraints, pads, f)?;
    append_input_constraint(&mut a, &mut b, constraints, pads, public_inputs, f)?;
    Ok((a, b))
}

/// Emit the final input equation, with N public inputs and weights a_i:
///
/// ```text
/// sum_{(p,k) in claim.terms} k*w[coordinate(p)]
///   + sum_{j=0}^{nprivate-1} (-a_{N+j})*w[j]
///   + (claim.constant - sum_{i=0}^{N-1} a_i*public[i]) = 0.
/// ```
/// Pad coefficients already have their constraint signs and pass through unchanged.
fn append_input_constraint<const W: usize, F: RuntimeField<W>>(
    a: &mut Vec<PolygeroLinearTerm<F::E>>,
    b: &mut Vec<F::E>,
    constraints: &Constraints<F::E>,
    pads: &CircuitPadLayout,
    public_inputs: &[F::E],
    f: &F,
) -> Result<(), String> {
    let claim = &constraints.input_claim;
    let weights = &constraints.input_weights;
    let npublic = public_inputs.len();
    let c = b.len();
    // The input sum is subtracted from the claim, so its known public part
    // contributes -sum_i a_i*public[i] to the constant b[c].
    let public_sum = blas::dot(&weights[..npublic], public_inputs, f);
    b.push(f.subf(&claim.constant, &public_sum));
    for w in 0..weights.len() - npublic {
        let weight = &weights[npublic + w];
        a.push(PolygeroLinearTerm {
            c,
            w,
            // Subtract the private part of that same sum, once.
            k: f.neg(weight),
        });
    }
    append_pad_terms(a, c, claim, pads)
}

use super::*;
use crate::{
    core::algebra::{AlgebraicField, SerializableField, SupportsU128Conversions},
    runtime::{
        algebra::{field::SupportsU64Conversions, gf2_128::Gf2_128Field, p256::P256Field},
        proto::{
            sumcheck_v2::{LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry},
            zk_v2::product_constraints,
        },
        sumcheck_v2::{symbolic::build_constraints, LayerChallenges},
    },
};

// Reconstruct all three coefficients and evaluate by Horner's rule, independently
// of the affine symbolic update, then compare each constraint residual.
#[allow(clippy::too_many_arguments)]
fn reference<const W: usize, F: RuntimeField<W> + SerializableField>(
    proof: &SumcheckProof<W, F>,
    pad_values: &SumcheckProof<W, F>,
    points: &[Vec<F::E>],
    alphas: &[F::E],
    weights: &[F::E],
    inputs: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut claim = f.zero();
    let mut residuals = Vec::new();
    for layer in 0..proof.layers.len() {
        let messages = &proof.layers[layer];
        let pads = &pad_values.layers[layer];
        for round in 0..messages.rounds.len() {
            let message = &messages.rounds[round];
            let pad = &pads.rounds[round];
            let c0 = f.addf(&message.coefficients[0], &pad.coefficients[0]);
            let c1 = f.addf(&message.coefficients[1], &pad.coefficients[1]);
            let c2 = f.subf(&claim, &c0);
            let z = &points[layer][round];
            claim = f.addf(&c0, &f.mulf(z, &f.addf(&c1, &f.mulf(z, &c2))));
        }
        let claims = [
            f.addf(&messages.claims[0], &pads.claims[0]),
            f.addf(&messages.claims[1], &pads.claims[1]),
        ];
        residuals.push(f.subf(&claim, &f.mulf(&claims[0], &claims[1])));
        claim = f.addf(&claims[0], &f.mulf(&alphas[layer], &claims[1]));
    }
    residuals.push(f.subf(
        &claim,
        &crate::runtime::algebra::blas::dot(weights, inputs, f),
    ));
    residuals
}

fn check_compilation<const W: usize, F: crate::runtime::algebra::ZkField<W>>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    for widths in [vec![2, 0, 1], vec![]] {
        let geometry = SumcheckProofGeometry {
            logw_layers: widths.clone(),
        };
        let proof = SumcheckProof {
            layers: widths
                .iter()
                .enumerate()
                .map(|(layer, &rounds)| LayerProof {
                    rounds: (0..rounds)
                        .map(|round| RoundPoly {
                            coefficients: [element(3 + (layer + round) as u64), element(11)],
                        })
                        .collect(),
                    claims: [element(7), element(13 + layer as u64)],
                })
                .collect(),
        };
        let pad_values = SumcheckProof {
            layers: widths
                .iter()
                .map(|&rounds| LayerProof {
                    rounds: (0..rounds)
                        .map(|_| RoundPoly {
                            coefficients: [element(17), element(19)],
                        })
                        .collect(),
                    claims: [element(23), element(29)],
                })
                .collect(),
        };
        // Include a challenge that erases the old claim and a zero alpha.
        let points: Vec<Vec<_>> = widths
            .iter()
            .enumerate()
            .map(|(layer, &rounds)| {
                (0..rounds)
                    .map(|round| {
                        if layer == 0 && round == 0 {
                            f.zero()
                        } else {
                            element(31)
                        }
                    })
                    .collect()
            })
            .collect();
        let alphas: Vec<_> = widths
            .iter()
            .enumerate()
            .map(|(layer, _)| if layer == 0 { f.zero() } else { element(37) })
            .collect();
        let input_weights = vec![element(41), f.zero(), element(43)];
        let inputs = vec![element(47), element(53), element(59)];
        let expected = reference(
            &proof,
            &pad_values,
            &points,
            &alphas,
            &input_weights,
            &inputs,
            f,
        );
        let make_constraints = || {
            let challenges = points
                .iter()
                .zip(&alphas)
                .map(|(point, alpha)| LayerChallenges {
                    constant: f.zero(),
                    linear: f.zero(),
                    point_l: point.clone(),
                    alpha: alpha.clone(),
                })
                .collect();
            build_constraints(&proof, challenges, input_weights.clone(), f)
        };
        let constraints = make_constraints();
        assert_eq!(
            constraints.residuals(&inputs, &pad_values, f).unwrap(),
            expected
        );
        for npublic in [0, 1, inputs.len()] {
            let nprivate = inputs.len() - npublic;
            let layout = geometry.pad_layout(nprivate);
            let (a, b) = compile_direct(&constraints, &layout, &inputs[..npublic], f).unwrap();
            let mut witness = inputs[npublic..].to_vec();
            for layer in &pad_values.layers {
                for round in &layer.rounds {
                    witness.extend_from_slice(&round.coefficients);
                }
                witness.extend_from_slice(&layer.claims);
                witness.push(f.mulf(&layer.claims[0], &layer.claims[1]));
            }
            let evaluate = |values: &[F::E]| {
                let mut residuals = b.clone();
                for term in &a {
                    f.fma(&mut residuals[term.c], &term.k, &values[term.w]);
                }
                residuals
            };
            assert_eq!(evaluate(&witness), expected);
            // Exercise the production compiler and packing handoff, independently
            // of the retained direct-field compiler. The direct packing row uses
            // input_sum - claim, the opposite sign of the reference's final row.
            let physical = crate::runtime::proto::zk_v2::PackingLayout::new(
                nprivate,
                witness.len() - nprivate,
                1,
            )
            .unwrap();
            let statement = compile(
                make_constraints(),
                &layout,
                &inputs[..npublic],
                &physical,
                f,
            )
            .unwrap();
            let backend = super::super::commitment::PackingCommitment::new(
                f.clone(),
                physical,
                crate::runtime::algebra::IdentityExtension::new(f.clone()),
            )
            .unwrap();
            let rows = crate::runtime::dual_packing::generic::reconstruct(
                &backend.parameters,
                &statement.claim,
                &crate::runtime::proto::dual_packing::PackingProof::Direct,
                &[],
            )
            .unwrap();
            let (native_a, mut native_b) = backend.authenticate::<W>(statement, &rows).unwrap();
            for term in native_a {
                f.fma(&mut native_b[term.c], &term.k, &witness[term.w]);
            }
            let final_row = expected.len() - 1;
            assert_eq!(&native_b[..final_row], &expected[..final_row]);
            assert_eq!(native_b[final_row], f.neg(&expected[final_row]));
            let products = product_constraints(nprivate, &geometry);
            assert!(products
                .iter()
                .all(|p| f.mulf(&witness[p.x], &witness[p.y]) == witness[p.z]));
            // The product slot must be enforced in both the linear row and
            // the quadratic commitment relation, including over prime fields.
            if let Some(product) = products.first() {
                f.add(&mut witness[product.z], &f.one());
                assert_ne!(evaluate(&witness), expected);
                assert_ne!(
                    f.mulf(&witness[product.x], &witness[product.y]),
                    witness[product.z]
                );
            }
        }
    }
}

#[test]
fn symbolic_and_compiled_constraints_match_numerical_binary() {
    let f = Gf2_128Field::new();
    check_compilation(&f, |x| f.u128_to_element(x as u128));
}

#[test]
fn symbolic_and_compiled_constraints_match_numerical_prime() {
    let f = P256Field::new();
    check_compilation(&f, |x| f.u64_to_element(x));
}

#[test]
fn prime_field_coefficients_preserve_zero_sum_signs() {
    let f = P256Field::new();
    let e = |x| f.u64_to_element(x);
    let proof = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![],
            claims: [e(2), e(3)],
        }],
    };
    let challenges = vec![LayerChallenges {
        constant: f.zero(),
        linear: f.zero(),
        point_l: vec![],
        alpha: e(5),
    }];
    let constraints = build_constraints(&proof, challenges, vec![e(7), e(11)], &f);
    let pads = SumcheckProofGeometry {
        logw_layers: vec![0],
    }
    .pad_layout(1);
    let (a, b) = compile_direct(&constraints, &pads, &[e(13)], &f).unwrap();

    // w = [private, p_A, p_B, p_A*p_B]. Starting from claim = 0 gives
    // -3*p_A - 2*p_B - w[3] - 6 = 0.
    // The next claim is (2+p_A) + 5*(3+p_B), hence the input equation is
    // p_A + 5*p_B - 11*private + (17 - 7*13) = 0.
    let expected = vec![
        (0, 1, f.neg(&e(3))),
        (0, 2, f.neg(&e(2))),
        (0, 3, f.mone()),
        (1, 0, f.neg(&e(11))),
        (1, 1, f.one()),
        (1, 2, e(5)),
    ];
    let actual: Vec<_> = a.into_iter().map(|term| (term.c, term.w, term.k)).collect();
    assert_eq!(actual, expected);
    assert_eq!(b, vec![f.neg(&e(6)), f.neg(&e(74))]);
}

#[test]
fn zero_weights_preserve_constant_constraint() {
    let f = Gf2_128Field::new();
    let constraints = Constraints {
        layers: vec![],
        input_claim: PadExpression {
            constant: f.one(),
            terms: vec![],
        },
        input_weights: vec![f.zero(); 3],
    };
    let pads = SumcheckProofGeometry {
        logw_layers: vec![],
    }
    .pad_layout(3);
    let (a, b) = compile_direct(&constraints, &pads, &[], &f).unwrap();
    assert_eq!(a.len(), 3);
    assert!(a.iter().all(|term| f.is_zero(&term.k)));
    // This equation is unsatisfiable even though every variable weight is zero.
    assert_eq!(b, vec![f.one()]);
    let physical = crate::runtime::proto::zk_v2::PackingLayout::new(3, 0, 1).unwrap();
    let statement = compile::<2, _>(constraints, &pads, &[], &physical, &f).unwrap();
    let backend = super::super::commitment::PackingCommitment::new(
        f.clone(),
        physical,
        crate::runtime::algebra::IdentityExtension::new(f.clone()),
    )
    .unwrap();
    let rows = crate::runtime::dual_packing::generic::reconstruct(
        &backend.parameters,
        &statement.claim,
        &crate::runtime::proto::dual_packing::PackingProof::Direct,
        &[],
    )
    .unwrap();
    let (native_a, native_b) = backend.authenticate::<2>(statement, &rows).unwrap();
    assert!(native_a.iter().all(|term| f.is_zero(&term.k)));
    assert_eq!(native_b, vec![f.one()]);
}

#[test]
fn rejects_mismatched_challenges_and_pad_layout() {
    let f = Gf2_128Field::new();
    let proof = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![],
            claims: [f.zero(); 2],
        }],
    };
    assert!(
        std::panic::catch_unwind(|| { build_constraints(&proof, vec![], vec![], &f) }).is_err()
    );
    let extra_round = vec![LayerChallenges {
        constant: f.zero(),
        linear: f.zero(),
        point_l: vec![f.zero()],
        alpha: f.one(),
    }];
    assert!(
        std::panic::catch_unwind(|| { build_constraints(&proof, extra_round, vec![], &f) })
            .is_err()
    );
    let layer_challenges = vec![LayerChallenges {
        constant: f.zero(),
        linear: f.zero(),
        point_l: vec![],
        alpha: f.one(),
    }];
    let constraints = build_constraints(&proof, layer_challenges, vec![], &f);
    let missing_pads = SumcheckProofGeometry {
        logw_layers: vec![],
    }
    .pad_layout(0);
    assert!(compile_direct(&constraints, &missing_pads, &[], &f).is_err());
    let pads = SumcheckProofGeometry {
        logw_layers: vec![0],
    }
    .pad_layout(0);
    assert!(compile_direct(&constraints, &pads, &[f.one()], &f).is_err());
}
