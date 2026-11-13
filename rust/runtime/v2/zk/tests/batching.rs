// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{blas, p256::P256Field},
        random::DeterministicRng,
        v2::transcript::Transcript,
    },
};

/// One layer asserting `x*y = public` and that the last private input is zero.
fn circuit(f: &P256Field, cached_logw: usize) -> Circuit<P256Field> {
    let mut layer = Layer::with_assertions(
        4,
        Stream::<Quadratic>::from_terms(vec![Quadratic {
            g: 0,
            l: 1,
            r: 2,
            k: 1,
        }]),
        Stream::<Linear>::from_terms(vec![
            Linear { g: 0, l: 0, k: 2 },
            Linear { g: 0, l: 3, k: 0 },
        ]),
        Stream::default(),
        |k| k == 0,
    );
    layer.logw = cached_logw;
    let raw = RawCircuitBuilder {
        ninput: 4,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.zero(), f.one(), f.mone()],
        layers: vec![layer],
    }
    .build();
    Circuit::from_raw(f, raw)
}

#[test]
fn batching_uses_widths_instead_of_cached_logw() {
    use crate::runtime::v2::sumcheck::{self, TranscriptSumcheck};
    let f = P256Field::new();
    for cached_logw in [0, 2, 41] {
        let circuit = circuit(&f, cached_logw);
        let geometry = sumcheck::circuit_geometry(&[&circuit]).unwrap();
        assert_eq!(geometry.logw_layers, [2]);
        let public = [f.u64_to_element(6)];
        let private = vec![f.u64_to_element(2), f.u64_to_element(3), f.zero()];
        let (pads, suffix) = sumcheck::sample_pads(&geometry, &mut DeterministicRng::new(42), &f);
        let mut values = private.clone();
        values.extend(suffix);
        let mut inputs = public.to_vec();
        inputs.extend(private);
        let mut tp = Transcript::new(b"prime-width-geometry");
        let mut tv = tp.fork_for_test();
        tp.borrow().write_sumcheck_statement(&circuit, &public, &f);
        let (proof, constraints) =
            sumcheck::evaluate_and_prove_circuits(&[&circuit], inputs, &pads, &mut tp.borrow(), &f)
                .unwrap();
        let claim = batch(&circuit, &public, constraints, &mut tp.borrow(), &f).unwrap();
        tv.borrow().write_sumcheck_statement(&circuit, &public, &f);
        let derived =
            sumcheck::derive_constraints_for_circuits(&[&circuit], &proof, &mut tv.borrow(), &f)
                .unwrap();
        let checked = batch(&circuit, &public, derived, &mut tv.borrow(), &f).unwrap();
        assert_eq!(claim.weights, checked.weights);
        assert_eq!(claim.target, checked.target);
        assert_eq!(blas::dot(&claim.weights, &values, &f), claim.target);
        assert_eq!(tp.bytes(32), tv.bytes(32));
    }
}
