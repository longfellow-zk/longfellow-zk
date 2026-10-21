// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Dense contraction of a layer's quadratic wiring into either input index.
use core_proto::{Layer, SerializableField};
use runtime_algebra::RuntimeField;

/// Contract either input index. Assertion coefficients never depend on lambda.
#[allow(clippy::too_many_arguments)]
pub fn contract<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    lambda: &[F::E],
    assertions: &[F::E],
    other: &[F::E],
    input: usize,
    f: &F,
) -> Vec<F::E> {
    assert!(input < 2);
    let mut result = vec![f.zero(); layer.nw().max(1)];
    let one = f.one();
    layer.for_each_term(constants, |term| {
        let g = term.g as usize;
        let coefficient = if f.is_zero(&term.k) {
            assertions[g].clone()
        } else if term.k == one {
            lambda[g].clone()
        } else {
            f.mulf(&lambda[g], &term.k)
        };
        let h = [term.h0 as usize, term.h1 as usize];
        f.fma(&mut result[h[input]], &coefficient, &other[h[1 - input]]);
    });
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{eq::next_weights, eval::assertion_outputs, transcript::assertion_weights};
    use core_algebra::{SupportsU128Conversions, SupportsU64Conversions};
    use core_proto::TermDelta;
    use runtime_algebra::SupportsSampling;
    use runtime_random::Transcript;

    fn check<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling<W>>(
        f: &F,
        element: impl Fn(u64) -> F::E,
    ) {
        // Ordinary output 0 and assertion output 1. The assertion's propagated
        // ordinary weight is deliberately zero and must not erase its product.
        let layer = Layer::new_compressed(
            3,
            2,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [0, 1],
                    k_index: 1,
                },
                TermDelta {
                    g: 1,
                    h: [2, 1],
                    k_index: 0,
                },
            ]],
            vec![0],
        );
        let constants = [f.zero(), element(3)];
        let lambda = [element(7), f.zero()];
        let outputs = assertion_outputs(&layer, &constants, 2, f).unwrap();
        assert_eq!(outputs, [false, true]);
        let mut transcript = Transcript::new(b"assertion-independence");
        let rho = assertion_weights(&outputs, 0, &mut transcript, f);
        assert_ne!(rho[1], f.zero());
        let wires = [element(2), element(5), element(11)];
        let h = contract(&layer, &constants, &lambda, &rho, &wires, 0, f);
        assert_eq!(h[2], f.mulf(&rho[1], &wires[2]));
        let point = [element(13), element(17)];
        let chi = crate::eq::weights(2, 3, &point, f);
        let mu = contract(&layer, &constants, &lambda, &rho, &chi, 1, f);
        let a = runtime_algebra::blas::dot(&chi, &wires, f);
        let b = runtime_algebra::blas::dot(&chi, &h, f);
        assert_eq!(b, runtime_algebra::blas::dot(&mu, &wires, f));
        let alpha = element(19);
        let next = next_weights(chi, &mu, &alpha, f);
        assert_eq!(
            runtime_algebra::blas::dot(&next, &wires, f),
            f.addf(&a, &f.mulf(&alpha, &b))
        );
        // The marker product is nonzero despite lambda[1]=0: a false zero
        // incoming claim cannot pass the honest first-hand reduction.
        assert_ne!(h[2], f.zero());
        let malformed = Layer::new_compressed(
            1,
            0,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 0,
                },
            ]],
            vec![0],
        );
        assert!(assertion_outputs(&malformed, &constants, 1, f).is_err());
    }

    #[test]
    fn functional_transition_and_independent_assertions_prime() {
        let f = runtime_algebra::p256::P256Field::new();
        check(&f, |x| f.u64_to_element(x));
    }
    #[test]
    fn functional_transition_and_independent_assertions_binary() {
        let f = runtime_algebra::gf2_128::Gf2_128Field::new();
        check(&f, |x| f.u128_to_element(x as u128));
    }
}
