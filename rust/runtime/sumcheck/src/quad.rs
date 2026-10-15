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

//! Dense hand polynomials and direct evaluation of a layer's wiring polynomial.
//! Terms stay in their segmented LFC2 representation and are streamed only once
//! per hand. No per-term HQuad or per-round circuit traversal is needed.

use core_proto::{Layer, SerializableField};
use runtime_algebra::RuntimeField;

/// Adds sum k*G(g)*other(h_other) to each destination coordinate h_hand.
/// The caller supplies a zeroed destination. A zero circuit coefficient denotes
/// a copy constraint and is replaced with beta, as in circuit evaluation.
#[allow(clippy::too_many_arguments)]
pub(crate) fn accumulate_hand<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    g: &[F::E],
    beta: &F::E,
    other: &[F::E],
    hand: usize,
    destination: &mut [F::E],
    f: &F,
) {
    assert!(hand < 2);
    let one = f.one();
    layer.for_each_term(
        constants,
        #[inline(always)]
        |term| {
            let coefficient = if f.is_zero(&term.k) { beta } else { &term.k };
            let weighted_g = if term.k == one {
                g[term.g as usize].clone()
            } else {
                f.mulf(coefficient, &g[term.g as usize])
            };
            let h = [term.h0 as usize, term.h1 as usize];
            f.fma(&mut destination[h[hand]], &weighted_g, &other[h[1 - hand]]);
        },
    );
}

/// Evaluates sum k*G(g)*EQ(h0, r0)*EQ(h1, r1) directly from the stored layer.
/// G already includes the two incoming output claims' equality weights and alpha.
/// This is the unscaled wiring value, even when either final witness claim is zero.
pub fn evaluate_quad<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    g: &[F::E],
    challenges: &[Vec<F::E>; 2],
    beta: &F::E,
    f: &F,
) -> F::E {
    let h0 = crate::eq::eq1(layer.logw(), layer.nw(), &challenges[0], f);
    let h1 = crate::eq::eq1(layer.logw(), layer.nw(), &challenges[1], f);
    let mut sum = f.zero_accum();
    let one = f.one();
    layer.for_each_term(
        constants,
        #[inline(always)]
        |term| {
            let coefficient = if f.is_zero(&term.k) { beta } else { &term.k };
            let weighted_g = if term.k == one {
                g[term.g as usize].clone()
            } else {
                f.mulf(coefficient, &g[term.g as usize])
            };
            let hands = f.mulf(&h0[term.h0 as usize], &h1[term.h1 as usize]);
            f.mac(&mut sum, &weighted_g, &hands);
        },
    );
    f.accum_reduce(&sum)
}

#[cfg(test)]
mod tests {
    use super::{accumulate_hand, evaluate_quad};
    use core_algebra::{SerializableField, SupportsU128Conversions, SupportsU64Conversions};
    use core_proto::{Layer, TermDelta};
    use runtime_algebra::{gf2_128::Gf2_128Field, p256::P256Field, RuntimeField};

    fn check_dense_hands<const W: usize, F: RuntimeField<W> + SerializableField>(
        f: &F,
        element: impl Fn(usize) -> F::E,
    ) {
        for nw in [0usize, 1, 3, 7, 8, 15] {
            let logw = nw.max(1).next_power_of_two().ilog2() as usize;
            let challenges: [Vec<_>; 2] = std::array::from_fn(|hand| {
                (0..logw).map(|bit| element(3 + 7 * hand + bit)).collect()
            });
            // Independent equality evaluation, bit by bit, without eq1/eq2.
            let equality = |index: usize, hand: usize| {
                let mut value = f.one();
                for (bit, r) in challenges[hand].iter().enumerate() {
                    let factor = if index & (1 << bit) == 0 {
                        f.subf(&f.one(), r)
                    } else {
                        r.clone()
                    };
                    f.mul(&mut value, &factor);
                }
                value
            };
            let witness: Vec<_> = (0..nw).map(|i| element(i + 2)).collect();
            let constants = [f.zero(), f.one(), element(7)];
            let beta = element(5);
            let g = [element(3), element(9)];
            let mut terms = Vec::new();
            for h0 in 0..nw {
                for h1 in 0..nw {
                    if (h0 + 3 * h1) % 4 != 1 {
                        for output in 0..2 {
                            terms.push((h0, h1, output, (h0 + h1 + output) % 3));
                        }
                    }
                }
            }
            // Deliberately reverse traversal: dense accumulation must not depend
            // on Morton/lexicographic order, sibling adjacency, or g grouping.
            terms.reverse();
            let mut previous = [0u32; 3];
            let mut deltas = Vec::new();
            let mut expected0 = vec![f.zero(); nw];
            let mut expected1 = vec![f.zero(); nw];
            for &(h0, h1, output, k) in &terms {
                deltas.push(TermDelta {
                    g: (output as u32).wrapping_sub(previous[0]),
                    h: [
                        (h0 as u32).wrapping_sub(previous[1]),
                        (h1 as u32).wrapping_sub(previous[2]),
                    ],
                    k_index: k as u32,
                });
                previous = [output as u32, h0 as u32, h1 as u32];
                let coefficient = if k == 0 { &beta } else { &constants[k] };
                let weighted_g = f.mulf(coefficient, &g[output]);
                f.fma(&mut expected0[h0], &weighted_g, &witness[h1]);
                f.fma(&mut expected1[h1], &weighted_g, &equality(h0, 0));
            }
            let layer = Layer::new_compressed(nw, logw, vec![deltas], vec![0]);
            let mut actual0 = vec![f.zero(); nw];
            let mut actual1 = vec![f.zero(); nw];
            let h0 = crate::eq::eq1(logw, nw, &challenges[0], f);
            assert_eq!(h0, (0..nw).map(|i| equality(i, 0)).collect::<Vec<_>>());
            accumulate_hand(&layer, &constants, &g, &beta, &witness, 0, &mut actual0, f);
            accumulate_hand(&layer, &constants, &g, &beta, &h0, 1, &mut actual1, f);
            assert_eq!(actual0, expected0);
            assert_eq!(actual1, expected1);
            let mut expected_value = f.zero();
            for (i, weight) in expected1.iter().enumerate() {
                f.fma(&mut expected_value, weight, &equality(i, 1));
            }
            assert_eq!(
                evaluate_quad(&layer, &constants, &g, &challenges, &beta, f),
                expected_value
            );
        }
    }

    #[test]
    fn dense_hand_polynomials_and_direct_evaluation_prime_field() {
        let f = P256Field::new();
        check_dense_hands(&f, |n| f.u64_to_element(n as u64));
    }

    #[test]
    fn dense_hand_polynomials_and_direct_evaluation_binary_field() {
        let f = Gf2_128Field::new();
        check_dense_hands(&f, |n| f.u128_to_element(n as u128));
    }
}
