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
    core::{
        algebra::{SupportsU128Conversions, SupportsU64Conversions},
        proto::{Layer, SerializableField, TermDelta},
    },
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        random::{RandomEngine, Transcript},
        sumcheck_v2::{
            monomial,
            quad::{bind_l, bind_r},
            transcript::assertion_weights,
        },
    },
};

fn check<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
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
    let layer = crate::core::proto::v2::quadratic_layer_fixture(layer, &constants, f);
    let a = [element(7), f.zero()];
    let mut transcript = Transcript::new(b"assertion-independence");
    let rho = assertion_weights(&layer, &constants, 0, &mut transcript, f);
    assert_eq!(rho.len(), 1);
    assert_ne!(rho[0], f.zero());
    let w = [element(2), element(5), element(11)];
    let q_l = bind_r(&layer, &constants, &a, &rho, &w, f);
    assert_eq!(q_l[2], f.mulf(&rho[0], &w[2]));
    let point = [element(13), element(17)];
    let m_l = monomial::weights(2, 3, &point, f);
    let q_r = bind_l(&layer, &constants, &a, &rho, &m_l, f);
    let w_u = blas::dot(&m_l, &w, f);
    let b = blas::dot(&m_l, &q_l, f);
    assert_eq!(b, blas::dot(&q_r, &w, f));
    let alpha = element(19);
    let mut next = m_l;
    blas::axpy(&mut next, &alpha, &q_r, f);
    assert_eq!(blas::dot(&next, &w, f), f.addf(&w_u, &f.mulf(&alpha, &b)));
    // The marker product is nonzero despite a[1]=0: a false zero
    // incoming claim cannot pass the honest first-hand reduction.
    assert_ne!(q_l[2], f.zero());
    check_repeated_output(f);
    check_quad_order(f, element);
}

fn check_repeated_output<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    f: &F,
) {
    let constants = [f.zero()];
    let mut transcript = Transcript::new(b"repeated-assertion-output");
    let repeated_output = Layer::new_compressed(
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
    let repeated_output =
        crate::core::proto::v2::quadratic_layer_fixture(repeated_output, &constants, f);
    // Repeated output indices still receive independent replacement coefficients.
    let mut expected = transcript.clone();
    expected.write_bytes(b"single-hand-assertions");
    expected.write_bytes(&1u64.to_le_bytes());
    let expected_rho = expected.elt_field_slice(2, f);
    let rho = assertion_weights(&repeated_output, &constants, 1, &mut transcript, f);
    assert_eq!(rho, expected_rho);
    assert_eq!(transcript.bytes(32), expected.bytes(32));
    let q_l = bind_r(
        &repeated_output,
        &constants,
        &[f.zero()],
        &rho,
        &[f.one()],
        f,
    );
    assert_eq!(q_l, [f.addf(&rho[0], &rho[1])]);
    assert_ne!(q_l[0], f.zero());
}

fn check_quad_order<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    let constants = [f.zero(), element(3)];
    let a = [element(7), f.zero()];
    let w = [element(2), element(5), element(11)];
    let point = [element(13), element(17)];
    let mut transcript = Transcript::new(b"quad-order");
    // Assertions at outputs 1 then 0, with an ordinary quad between them.
    // Check sum_{g,r} a[g] QUAD[g,l,r] W[r] directly so an output-index
    // permutation cannot pass merely by being repeated in both bindings.
    let reordered = Layer::new_compressed(
        3,
        2,
        vec![vec![
            TermDelta {
                g: 1,
                h: [0, 1],
                k_index: 0,
            },
            TermDelta {
                g: u32::MAX,
                h: [1, 0],
                k_index: 1,
            },
            TermDelta {
                g: 0,
                h: [1, u32::MAX],
                k_index: 0,
            },
        ]],
        vec![0],
    );
    let reordered = crate::core::proto::v2::quadratic_layer_fixture(reordered, &constants, f);
    let rho = assertion_weights(&reordered, &constants, 2, &mut transcript, f);
    assert_eq!(rho.len(), 2);
    let q_l = bind_r(&reordered, &constants, &a, &rho, &w, f);
    assert_eq!(
        q_l,
        [
            f.mulf(&rho[0], &w[1]),
            f.mulf(&f.mulf(&a[0], &constants[1]), &w[1]),
            f.mulf(&rho[1], &w[0]),
        ]
    );
    let m_l = monomial::weights(2, 3, &point, f);
    let q_r = bind_l(&reordered, &constants, &a, &rho, &m_l, f);
    assert_eq!(blas::dot(&m_l, &q_l, f), blas::dot(&q_r, &w, f),);
}

#[test]
fn functional_transition_and_independent_assertions_prime() {
    let f = crate::runtime::algebra::p256::P256Field::new();
    check(&f, |x| f.u64_to_element(x));
}
#[test]
fn functional_transition_and_independent_assertions_binary() {
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    check(&f, |x| f.u128_to_element(x as u128));
}

/// Check the initial weights and the next PRF bytes independently of the
/// prover/verifier roundtrip. Both roles could otherwise share the same extra
/// sampling bug. Include a scalar output, which must sample no coordinates.
fn check_output_sampling<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    f: &F,
) {
    use crate::core::proto::v2::{Circuit, RawCircuit};
    for (logv, noutput) in [(0, 1), (1, 2), (3, 5), (7, 93)] {
        let circuit = Circuit {
            id: [0; 32],
            coefficient_classes: Default::default(),
            raw: RawCircuit {
                ninput: noutput,
                npublic_input: 0,
                noutput,
                logv,
                subfield_boundary: 0,
                constants: vec![],
                layers: vec![],
            },
        };
        let mut actual = Transcript::new(b"v2-output-challenges");
        let weights = crate::runtime::sumcheck_v2::transcript::begin(&circuit, &mut actual, f);

        let mut expected = Transcript::new(b"v2-output-challenges");
        expected.write_bytes(b"longfellow-sumcheck-v2-projective");
        let point = expected.elt_field_slice(logv, f);
        assert_eq!(weights.len(), noutput);
        for (g, weight) in weights.iter().enumerate() {
            let mut product = f.one();
            for (bit, coordinate) in point.iter().enumerate() {
                if g & (1 << bit) != 0 {
                    f.mul(&mut product, coordinate);
                }
            }
            assert_eq!(*weight, product);
        }
        assert_eq!(actual.bytes(32), expected.bytes(32), "logv={logv}");
    }
}

#[test]
fn output_sampling_uses_exact_dimension_prime() {
    check_output_sampling(&crate::runtime::algebra::p256::P256Field::new());
}

#[test]
fn output_sampling_uses_exact_dimension_binary() {
    check_output_sampling(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}
