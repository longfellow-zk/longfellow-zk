// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    compile::logic::Logic,
    core::algebra::{BareField, SupportsU64Conversions},
    mldsa::{
        compile::circuits::polynomial::PolynomialW,
        proto::{N, ZETAS},
    },
};
pub(super) struct Ntt<'a, L: Logic> {
    pub logic: &'a L,
    pub ntt_stride: usize,
}
impl<L: Logic> Ntt<'_, L>
where L::F: SupportsU64Conversions
{
    fn scalar(&self, x: u32) -> <L::F as BareField>::E {
        self.logic.field().u64_to_element(x as u64)
    }
    pub(super) fn ntt(&self, polynomial: &PolynomialW<L>) -> PolynomialW<L> {
        let mut result = polynomial.clone();
        let mut k = 1;
        let mut len = N / 2;
        let mut stage = 0;
        while len >= 1 {
            for start in (0..N).step_by(2 * len) {
                let zeta = self.scalar(ZETAS[k]);
                k += 1;
                for j in start..start + len {
                    let product = self.logic.mulk(&zeta, &result.coefficients[j + len]);
                    let low = self.logic.add(&result.coefficients[j], &product);
                    let high = self.logic.sub(&result.coefficients[j], &product);
                    result.coefficients[j] = low;
                    result.coefficients[j + len] = high;
                }
            }
            stage += 1;
            // Leave the final stage available to fuse with its equality.
            // Earlier cuts prevent exponential expansion of the FFT graph.
            if len > 1 && self.ntt_stride != 0 && stage % self.ntt_stride == 0 {
                for coefficient in &mut result.coefficients {
                    *coefficient = self.logic.precious(coefficient);
                }
            }
            len >>= 1;
        }
        debug_assert_eq!(k, N);
        result
    }

    pub(super) fn assert_ntt(&self, a: &PolynomialW<L>, b: &PolynomialW<L>) -> L::Assertions {
        let computed = self.ntt(a);
        self.logic.assert_mapi("ntt", 0..N, |i| {
            self.logic
                .assert_eq("coefficient", &computed.coefficients[i], &b.coefficients[i])
        })
    }
}
