// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
// Inverse UseHint adapted from GordieHowe, Copyright 2026 Chad Sharp and Paul Grubbs.
use super::ntt::Ntt;
use crate::{
    compile::{
        algebra::fp24_ext6::CompileFp24Ext6,
        compiler::{CompilerAssertions, CompilerLogic},
        logic::{Logic, LogicIO, K_FIRST_WIRE_POSITION},
    },
    core::algebra::SupportsU64Conversions,
    mldsa::{
        compile::circuits::polynomial::PolynomialW,
        proto::{MlDsaParams, N},
    },
};
struct PublicKeyW<L: Logic> {
    a_hat: Vec<Vec<PolynomialW<L>>>,
    ntt_t1: Vec<PolynomialW<L>>,
}

pub(crate) fn build<'a, P: MlDsaParams>(
    logic: CompilerLogic<'a, CompileFp24Ext6>,
    ntt_stride: usize,
) -> (CompilerAssertions<'a, CompileFp24Ext6>, usize) {
    let mut pos = K_FIRST_WIRE_POSITION;
    let npublic = pos;
    // Booleanity and range checks belong to the binary relation. The adapter
    // links each native coefficient to the corresponding group of checked bits.
    let shifted_z: Vec<_> = (0..P::L)
        .map(|_| PolynomialW::input(&logic, &mut pos))
        .collect();
    let raw: Vec<_> = (0..P::K)
        .map(|_| PolynomialW::input(&logic, &mut pos))
        .collect();
    let low: Vec<_> = (0..P::K)
        .map(|_| PolynomialW::input(&logic, &mut pos))
        .collect();
    let positive: Vec<_> = (0..N).map(|_| logic.next(&mut pos)).collect();
    let negative: Vec<_> = (0..N).map(|_| logic.next(&mut pos)).collect();
    let key = {
        let a_hat = (0..P::K)
            .map(|_| {
                (0..P::L)
                    .map(|_| PolynomialW::input(&logic, &mut pos))
                    .collect()
            })
            .collect();
        let gadget = Ntt {
            logic: &logic,
            ntt_stride,
        };
        let ntt_t1 = (0..P::K)
            .map(|_| {
                let coefficients = std::array::from_fn(|_| {
                    logic.mulk(
                        &logic.field().u64_to_element(1 << 13),
                        &logic.next(&mut pos),
                    )
                });
                gadget.ntt(&PolynomialW { coefficients })
            })
            .collect();
        PublicKeyW { a_hat, ntt_t1 }
    };
    let approximation: Vec<_> = (0..P::K)
        .map(|_| PolynomialW::input(&logic, &mut pos))
        .collect();
    let ntt_z: Vec<_> = (0..P::L)
        .map(|_| PolynomialW::input(&logic, &mut pos))
        .collect();
    let ntt_c = PolynomialW::input(&logic, &mut pos);
    let scalar = |x: u32| logic.konst(&logic.field().u64_to_element(u64::from(x)));
    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    let centered_z: Vec<_> = shifted_z
        .iter()
        .map(|row| PolynomialW {
            coefficients: std::array::from_fn(|i| {
                logic.precious(&logic.sub(&row.coefficients[i], &scalar(bound - 1)))
            }),
        })
        .collect();
    let c = PolynomialW {
        coefficients: std::array::from_fn(|i| {
            logic.precious(&logic.sub(&positive[i], &negative[i]))
        }),
    };
    let gadget = Ntt {
        logic: &logic,
        ntt_stride,
    };
    let mut assertions = Vec::new();
    for i in 0..P::L {
        assertions.push(gadget.assert_ntt(&centered_z[i], &ntt_z[i]));
    }
    assertions.push(gadget.assert_ntt(&c, &ntt_c));
    let az: Vec<PolynomialW<CompilerLogic<'a, CompileFp24Ext6>>> = key
        .a_hat
        .iter()
        .map(|row| PolynomialW {
            coefficients: std::array::from_fn(|i| {
                logic.sum(
                    &row.iter()
                        .zip(&ntt_z)
                        .map(|(matrix, transformed_z)| {
                            logic.mul(&matrix.coefficients[i], &transformed_z.coefficients[i])
                        })
                        .collect::<Vec<_>>(),
                )
            }),
        })
        .collect();
    let ct1: Vec<PolynomialW<CompilerLogic<'a, CompileFp24Ext6>>> = key
        .ntt_t1
        .iter()
        .map(|row| PolynomialW {
            coefficients: std::array::from_fn(|i| {
                logic.mul(&ntt_c.coefficients[i], &row.coefficients[i])
            }),
        })
        .collect();
    // NTT(w) = A_hat * NTT(z) - t1_hat * NTT(c) is equivalent to the
    // inverse-NTT check, but does not expand every product into 256 equations.
    for row in 0..P::K {
        let expected = PolynomialW {
            coefficients: std::array::from_fn(|i| {
                logic.sub(&az[row].coefficients[i], &ct1[row].coefficients[i])
            }),
        };
        assertions.push(gadget.assert_ntt(&approximation[row], &expected));
    }
    for (row, approximate) in approximation.iter().enumerate() {
        for i in 0..N {
            let high_coefficient = &raw[row].coefficients[i];
            let low_coefficient = &low[row].coefficients[i];
            let reconstructed = logic.add(
                &logic.mul(&scalar(2 * P::GAMMA2), high_coefficient),
                &logic.sub(low_coefficient, &scalar(P::GAMMA2)),
            );
            assertions.push(logic.assert_eq(
                "decomposition",
                &approximate.coefficients[i],
                &reconstructed,
            ));
        }
    }

    (
        logic.assert_all("split_mldsa_arithmetic", &assertions),
        npublic,
    )
}
