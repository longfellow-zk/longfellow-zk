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
        algebra::{RegisteredField, SupportsU128Conversions, SupportsU64Conversions},
        proto::{
            v1::{Layer, TermDelta},
            v2::quadratic_layer_fixture,
        },
    },
    runtime::{
        algebra::{blas, gf2_128::Gf2_128Field, p256::P256Field, RuntimeField, SupportsSampling},
        v2::{
            sumcheck::{
                fragments::Schedule,
                monomial,
                quad::{bind_l, bind_r},
                split::SplitLayer,
            },
            transcript::Transcript,
        },
    },
};

fn sample_assertions<
    'a,
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    layer: SplitLayer<'a>,
    stage: usize,
    transcript: &mut Transcript,
    f: &F,
) -> (SplitLayer<'a>, Vec<F::E>) {
    // One fragment: its quadratic markers, then its linear markers.
    let n = layer.assertion_counts().iter().sum();
    transcript.send_for_test(&(stage as u64).to_le_bytes());
    let rho = transcript
        .borrow()
        .draw(|r| r.elements(f, n).collect::<Vec<_>>());
    (layer, rho)
}

fn check<const W: usize, F: RuntimeField<W> + RegisteredField + SupportsSampling>(
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
                k_index: 3,
            },
            TermDelta {
                g: 1,
                h: [2, 1],
                k_index: 0,
            },
        ]],
        vec![0],
    );
    let constants = [f.zero(), f.one(), f.mone(), element(3)];
    let raw_layer = quadratic_layer_fixture(layer, &constants, f);
    let layer = crate::runtime::v2::sumcheck::split::SplitLayer::new(&raw_layer);
    let a = [element(7), f.zero()];
    let mut transcript = Transcript::for_test(b"assertion-independence");
    let (layer, rho) = sample_assertions(layer, 0, &mut transcript, f);
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
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    f: &F,
) {
    let constants = [f.zero()];
    let mut transcript = Transcript::for_test(b"repeated-assertion-output");
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
    let raw_repeated_output = quadratic_layer_fixture(repeated_output, &constants, f);
    let repeated_output =
        crate::runtime::v2::sumcheck::split::SplitLayer::new(&raw_repeated_output);
    // Repeated output indices still receive independent replacement coefficients.
    let mut expected = transcript.fork_for_test();
    expected.send_for_test(&1u64.to_le_bytes());
    let expected_rho = expected
        .borrow()
        .draw(|r| r.elements(f, 2).collect::<Vec<_>>());
    let (repeated_output, rho) = sample_assertions(repeated_output, 1, &mut transcript, f);
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

fn check_quad_order<const W: usize, F: RuntimeField<W> + RegisteredField + SupportsSampling>(
    f: &F,
    element: impl Fn(u64) -> F::E,
) {
    let constants = [f.zero(), f.one(), f.mone(), element(3)];
    let a = [element(7), f.zero()];
    let w = [element(2), element(5), element(11)];
    let point = [element(13), element(17)];
    let mut transcript = Transcript::for_test(b"quad-order");
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
                k_index: 3,
            },
            TermDelta {
                g: 0,
                h: [1, u32::MAX],
                k_index: 0,
            },
        ]],
        vec![0],
    );
    let raw_reordered = quadratic_layer_fixture(reordered, &constants, f);
    let reordered = crate::runtime::v2::sumcheck::split::SplitLayer::new(&raw_reordered);
    let (reordered, rho) = sample_assertions(reordered, 2, &mut transcript, f);
    assert_eq!(rho.len(), 2);
    let q_l = bind_r(&reordered, &constants, &a, &rho, &w, f);
    assert_eq!(
        q_l,
        [
            f.mulf(&rho[0], &w[1]),
            f.mulf(&f.mulf(&a[0], &constants[3]), &w[1]),
            f.mulf(&rho[1], &w[0]),
        ]
    );
    let m_l = monomial::weights(2, 3, &point, f);
    let q_r = bind_l(&reordered, &constants, &a, &rho, &m_l, f);
    assert_eq!(blas::dot(&m_l, &q_l, f), blas::dot(&q_r, &w, f),);
}

#[test]
fn functional_transition_and_independent_assertions_prime() {
    let f = P256Field::new();
    check(&f, |x| f.u64_to_element(x));
}
#[test]
fn functional_transition_and_independent_assertions_binary() {
    let f = Gf2_128Field::new();
    check(&f, |x| f.u128_to_element(x as u128));
}

/// Check the initial weights and the next PRF bytes independently of the
/// prover/verifier roundtrip. Both roles could otherwise share the same extra
/// sampling bug. Include a scalar output, which receives one independent weight.
fn check_output_sampling<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    f: &F,
) {
    use crate::core::proto::v2::{Circuit, RawCircuitBuilder};
    for (logv, noutput) in [(0, 1), (1, 2), (3, 5), (7, 93)] {
        let circuit = Circuit::with_test_id(
            [0; 32],
            RawCircuitBuilder {
                ninput: noutput,
                npublic_input: 0,
                noutput,
                logv,
                constants: vec![],
                layers: vec![],
            }
            .build(),
        );
        // A zero-layer circuit's top weights are its input assertions.
        let mut actual = Transcript::for_test(b"v2-output-challenges");
        let schedule = Schedule::new(&[&circuit], f).unwrap();
        let weights = schedule
            .draw_top(&[&circuit], &mut actual.borrow(), f)
            .outputs;
        let mut expected = Transcript::for_test(b"v2-output-challenges");
        let expected_weights = expected
            .borrow()
            .draw(|r| r.elements(f, noutput).collect::<Vec<_>>());
        assert_eq!(weights, expected_weights);
        assert_eq!(actual.bytes(32), expected.bytes(32), "logv={logv}");
    }
}

#[test]
fn output_sampling_uses_independent_weights_prime() {
    check_output_sampling(&P256Field::new());
}

#[test]
fn output_sampling_uses_independent_weights_binary() {
    check_output_sampling(&Gf2_128Field::new());
}
