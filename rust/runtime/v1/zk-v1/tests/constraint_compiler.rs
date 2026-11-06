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

use super::*;
use crate::{
    core::algebra::{AlgebraicField, SupportsU128Conversions},
    runtime::{
        algebra::{
            field::SupportsU64Conversions, gf2_128::Gf2_128Field, p256::P256Field,
            InterpolationField,
        },
        proto::sumcheck_v1::{LayerProof, RoundPoly, SumcheckProof},
        sumcheck_v1::{LagrangeBasis, LayerVerifierData, Poly, RoundCoefficients, VerifierData},
    },
};

// Independent numerical recurrence using full three-point interpolation.
#[allow(clippy::too_many_arguments)]
fn reference<const W: usize, F: InterpolationField<W>>(
    proof: &SumcheckProof<W, F>,
    pads: &SumcheckProof<W, F>,
    points: &[[Vec<F::E>; 2]],
    alphas: &[F::E],
    wiring: &[F::E],
    input_alpha: &F::E,
    weights: &[F::E],
    inputs: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut endpoints = [f.zero(), f.zero()];
    let mut residuals = Vec::new();
    for (layer, (messages, layer_pads)) in proof.layers.iter().zip(&pads.layers).enumerate() {
        let mut claim = f.addf(&endpoints[0], &f.mulf(&alphas[layer], &endpoints[1]));
        for (round, _) in messages.hp[0].iter().enumerate() {
            for (hand, hand_points) in points[layer].iter().enumerate() {
                let message = &messages.hp[hand][round];
                let pad = &layer_pads.hp[hand][round];
                let g0 = f.addf(&message.evaluations[0], &pad.evaluations[0]);
                let g1 = f.subf(&claim, &g0);
                let g2 = f.addf(&message.evaluations[1], &pad.evaluations[1]);
                claim = Poly::<3, W, F> {
                    evaluations: [g0, g1, g2],
                }
                .eval_lagrange(&hand_points[round], f);
            }
        }
        endpoints = std::array::from_fn(|i| f.addf(&messages.claims[i], &layer_pads.claims[i]));
        let product = f.mulf(&endpoints[0], &endpoints[1]);
        residuals.push(f.subf(&claim, &f.mulf(&wiring[layer], &product)));
    }
    let input_claim = f.addf(&endpoints[0], &f.mulf(input_alpha, &endpoints[1]));
    residuals.push(f.subf(
        &crate::runtime::algebra::blas::dot(weights, inputs, f),
        &input_claim,
    ));
    residuals
}

fn check_compilation<const W: usize, F: InterpolationField<W>>(
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
                    hp: std::array::from_fn(|hand| {
                        (0..rounds)
                            .map(|round| RoundPoly {
                                evaluations: [
                                    element(3 + (layer + round + hand) as u64),
                                    element(11),
                                ],
                            })
                            .collect()
                    }),
                    claims: [element(7), element(13 + layer as u64)],
                })
                .collect(),
        };
        let pads = SumcheckProof {
            layers: widths
                .iter()
                .map(|&rounds| LayerProof {
                    hp: std::array::from_fn(|hand| {
                        (0..rounds)
                            .map(|round| RoundPoly {
                                evaluations: [
                                    element(17 + hand as u64),
                                    element(19 + round as u64),
                                ],
                            })
                            .collect()
                    }),
                    claims: [element(23), element(29)],
                })
                .collect(),
        };
        let points: Vec<[Vec<_>; 2]> = widths
            .iter()
            .enumerate()
            .map(|(layer, &rounds)| {
                std::array::from_fn(|hand| {
                    (0..rounds)
                        .map(|round| {
                            if layer == 0 && hand == 0 && round == 0 {
                                f.poly_evaluation_point(0)
                            } else {
                                element(31 + hand as u64)
                            }
                        })
                        .collect()
                })
            })
            .collect();
        let alphas: Vec<_> = widths
            .iter()
            .enumerate()
            .map(|(layer, _)| if layer == 0 { f.zero() } else { element(37) })
            .collect();
        let wiring: Vec<_> = widths
            .iter()
            .enumerate()
            .map(|(layer, _)| {
                if layer == 1 {
                    f.zero()
                } else {
                    element(67 + layer as u64)
                }
            })
            .collect();
        let basis = LagrangeBasis::new(f);
        let data = VerifierData {
            layers: points
                .iter()
                .enumerate()
                .map(|(layer, point)| LayerVerifierData {
                    rounds: std::array::from_fn(|hand| {
                        point[hand]
                            .iter()
                            .map(|r| RoundCoefficients::new(&basis, r, f))
                            .collect()
                    }),
                    alpha: alphas[layer].clone(),
                    bound_quad: wiring[layer].clone(),
                })
                .collect(),
            input_alpha: element(61),
            input_weights: vec![element(41), f.zero(), element(43)],
        };
        let inputs = vec![element(47), element(53), element(59)];
        let expected = reference(
            &proof,
            &pads,
            &points,
            &alphas,
            &wiring,
            &data.input_alpha,
            &data.input_weights,
            &inputs,
            f,
        );
        let relations = crate::runtime::sumcheck_v1::symbolic::verify(&proof, data, f).unwrap();
        assert_eq!(relations.evaluate(&inputs, &pads, f).unwrap(), expected);
        for npublic in [0, 1, inputs.len()] {
            let nprivate = inputs.len() - npublic;
            let layout = geometry.pad_layout(nprivate);
            let (a, b) = compile(&relations, &layout, &inputs[..npublic], f).unwrap();
            let mut witness = inputs[npublic..].to_vec();
            for layer in &pads.layers {
                for round in 0..layer.hp[0].len() {
                    for hand in &layer.hp {
                        witness.extend_from_slice(&hand[round].evaluations);
                    }
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
            let products = product_constraints(nprivate, &geometry);
            assert!(products
                .iter()
                .all(|p| f.mulf(&witness[p.x], &witness[p.y]) == witness[p.z]));
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
fn relations_and_compiled_constraints_match_numerical_binary() {
    let f = Gf2_128Field::new();
    check_compilation(&f, |x| f.u128_to_element(x as u128));
}

#[test]
fn relations_and_compiled_constraints_match_numerical_prime() {
    let f = P256Field::new();
    check_compilation(&f, |x| f.u64_to_element(x));
}

#[test]
fn zero_weights_preserve_constant_constraint() {
    use crate::runtime::sumcheck_v1::symbolic::InputRelation;
    let f = Gf2_128Field::new();
    let relations = VerificationRelations {
        layers: vec![],
        input: InputRelation {
            weights: vec![f.zero(); 3],
            linear: PadExpression {
                constant: f.one(),
                terms: vec![],
            },
        },
    };
    let pads = SumcheckProofGeometry {
        logw_layers: vec![],
    }
    .pad_layout(3);
    let (a, b) = compile(&relations, &pads, &[], &f).unwrap();
    assert_eq!(a.len(), 3);
    assert!(a.iter().all(|term| f.is_zero(&term.k)));
    assert_eq!(b, vec![f.one()]);
}
#[test]
fn rejects_mismatched_verifier_data_and_pad_layout() {
    let f = Gf2_128Field::new();
    let proof = SumcheckProof {
        layers: vec![LayerProof {
            hp: [vec![], vec![]],
            claims: [f.zero(); 2],
        }],
    };
    let missing_layers = VerifierData {
        layers: vec![],
        input_alpha: f.one(),
        input_weights: vec![],
    };
    assert!(crate::runtime::sumcheck_v1::symbolic::verify(&proof, missing_layers, &f).is_err());
    let extra_round = VerifierData {
        layers: vec![LayerVerifierData {
            rounds: [
                vec![RoundCoefficients {
                    l1: f.one(),
                    l0_minus_l1: f.zero(),
                    l2: f.zero(),
                }],
                vec![],
            ],
            alpha: f.one(),
            bound_quad: f.one(),
        }],
        input_alpha: f.one(),
        input_weights: vec![],
    };
    assert!(crate::runtime::sumcheck_v1::symbolic::verify(&proof, extra_round, &f).is_err());
    let valid_data = VerifierData {
        layers: vec![LayerVerifierData {
            rounds: [vec![], vec![]],
            alpha: f.one(),
            bound_quad: f.one(),
        }],
        input_alpha: f.one(),
        input_weights: vec![],
    };
    let relations = crate::runtime::sumcheck_v1::symbolic::verify(&proof, valid_data, &f).unwrap();
    let missing_pads = SumcheckProofGeometry {
        logw_layers: vec![],
    }
    .pad_layout(0);
    assert!(compile(&relations, &missing_pads, &[], &f).is_err());
    let pads = SumcheckProofGeometry {
        logw_layers: vec![0],
    }
    .pad_layout(0);
    assert!(compile(&relations, &pads, &[f.one()], &f).is_err());
}
