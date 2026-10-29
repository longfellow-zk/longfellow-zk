// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
// Three-stream arithmetic. k=zero marks assertions; all other
// coefficients, including +/-1, take precisely the general field operations.
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic},
    },
    runtime::{
        algebra::{blas, RuntimeField},
        sumcheck_v2::monomial,
    },
};
pub(super) fn bind_l<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b: &[F::E],
    f: &F,
) -> Vec<F::E> {
    assert_eq!(assertions.len(), layer.assertion_counts().iter().sum());
    let mut rho = assertions[..layer.assertion_counts()[0]].iter();
    let mut q = vec![f.zero(); layer.nw];
    layer.quadratic.for_each(|Quadratic { g, l, r, k }| {
        let coefficient = if k == 0 {
            rho.next().unwrap().clone()
        } else {
            f.mulf(&a[g as usize], &constants[k as usize])
        };
        f.fma(&mut q[r as usize], &coefficient, &b[l as usize]);
    });
    q
}
#[cfg(any(test, feature = "prover"))]
pub(super) fn bind_r<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    w: &[F::E],
    f: &F,
) -> Vec<F::E> {
    assert_eq!(assertions.len(), layer.assertion_counts().iter().sum());
    let mut rho = assertions[..layer.assertion_counts()[0]].iter();
    let mut q = vec![f.zero(); layer.nw];
    layer.quadratic.for_each(|Quadratic { g, l, r, k }| {
        let coefficient = if k == 0 {
            rho.next().unwrap().clone()
        } else {
            f.mulf(&a[g as usize], &constants[k as usize])
        };
        f.fma(&mut q[l as usize], &coefficient, &w[r as usize]);
    });
    add_linear(
        layer,
        constants,
        a,
        &assertions[layer.assertion_counts()[0]..],
        &mut q,
        f,
    );
    q
}
#[cfg(any(test, feature = "prover"))]
pub(super) fn add_linear<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    q: &mut [F::E],
    f: &F,
) {
    let mut rho = assertions.iter();
    layer.linear.for_each(|Linear { g, l, k }| {
        if k == 0 {
            f.add(&mut q[l as usize], rho.next().unwrap());
        } else {
            f.fma(&mut q[l as usize], &a[g as usize], &constants[k as usize]);
        }
    });
}
pub(super) fn weights_next_affine<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point: &[F::E],
    alpha: &F::E,
    f: &F,
) -> (Vec<F::E>, F::E) {
    let mut weights = monomial::weights(layer.logw, layer.nw, point, f);
    let mut linear = f.zero();
    let mut rho = assertions[layer.assertion_counts()[0]..].iter();
    layer.linear.for_each(|Linear { g, l, k }| {
        let coefficient = if k == 0 {
            rho.next().unwrap().clone()
        } else {
            f.mulf(&a[g as usize], &constants[k as usize])
        };
        f.fma(&mut linear, &coefficient, &weights[l as usize]);
    });
    let q = bind_l(layer, constants, a, assertions, &weights, f);
    blas::axpy(&mut weights, alpha, &q, f);
    (weights, linear)
}
pub(super) fn affine_constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    f: &F,
) -> F::E {
    let mut c = f.zero();
    layer
        .constant
        .for_each(|Constant { g, k }| f.fma(&mut c, &a[g as usize], &constants[k as usize]));
    c
}

/// Frozen three-stream layer loop used only to check proof/transcript identity.
pub(super) fn prove_core<
    const W: usize,
    F: RuntimeField<W> + SerializableField + crate::runtime::algebra::SupportsSampling,
>(
    witnesses: Vec<Vec<F::E>>,
    pads: &crate::runtime::sumcheck_v2::SumcheckProof<W, F>,
    circuit: &crate::core::proto::v2::Circuit<F>,
    t: &mut crate::runtime::random::Transcript,
    f: &F,
) -> (
    crate::runtime::sumcheck_v2::SumcheckProof<W, F>,
    crate::runtime::sumcheck_v2::symbolic::Constraints<F::E>,
) {
    use crate::runtime::{
        random::RandomEngine,
        sumcheck_v2::{prover, symbolic, transcript},
    };
    let mut a = transcript::begin(circuit, t, f);
    let mut claim = f.zero();
    let mut layers = Vec::new();
    let mut challenges = Vec::new();
    for (index, w) in witnesses.into_iter().enumerate() {
        let layer = &circuit.raw.layers[index];
        let constants = &circuit.raw.constants;
        t.write_bytes(b"single-hand-assertions");
        t.write_bytes(&(index as u64).to_le_bytes());
        let rho: Vec<_> = (0..layer.assertion_counts().iter().sum::<usize>())
            .map(|_| t.elt_field(f))
            .collect();
        let q = bind_r(layer, constants, &a, &rho, &w, f);
        let constant = affine_constant(layer, constants, &a, f);
        let claim0 = f.subf(&claim, &constant);
        let (proof, mut c, mut next) =
            prover::prove_dot_product(w, q, &pads.layers[index], claim0, t, f);
        let (weights, linear) =
            weights_next_affine(layer, constants, &a, &rho, &c.point_l, &c.alpha, f);
        f.fnms(&mut next, &c.alpha, &linear);
        c.constant = constant;
        c.linear = linear;
        a = weights;
        claim = next;
        layers.push(proof);
        challenges.push(c);
    }
    let proof = crate::runtime::sumcheck_v2::SumcheckProof { layers };
    let constraints = symbolic::build_constraints(&proof, challenges, a, f);
    (proof, constraints)
}

// Frozen witness evaluation over the original three streams.
pub(super) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    circuit.validate_v2()?;
    let mut saved = Vec::with_capacity(circuit.raw.layers.len());
    for (index, layer) in circuit.raw.layers.iter().enumerate().rev() {
        let noutput = if index == 0 {
            circuit.raw.noutput
        } else {
            circuit.raw.layers[index - 1].nw
        };
        let outputs = eval_layer(&w, layer, &circuit.raw.constants, noutput, f).map_err(|e| {
            format!("Witness does not satisfy circuit constraints at layer {index}: {e}")
        })?;
        saved.push(w);
        w = outputs;
    }
    for (g, x) in w.iter().enumerate() {
        if !f.is_zero(x) {
            return Err(format!("Circuit output at index {g} is not zero"));
        }
    }
    saved.reverse();
    Ok(saved)
}
pub(super) fn eval_layer<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &Layer,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut out = vec![f.zero(); noutput];
    layer.quadratic.try_for_each(|Quadratic { g, l, r, k }| {
        let product = f.mulf(&w[l as usize], &w[r as usize]);
        if k == 0 {
            if !f.is_zero(&product) {
                return Err("quadratic assertion not satisfied".to_string());
            }
        } else {
            f.fma(&mut out[g as usize], &constants[k as usize], &product);
        }
        Ok(())
    })?;
    layer.linear.try_for_each(|Linear { g, l, k }| {
        if k == 0 {
            if !f.is_zero(&w[l as usize]) {
                return Err("linear assertion not satisfied".to_string());
            }
        } else {
            f.fma(&mut out[g as usize], &constants[k as usize], &w[l as usize]);
        }
        Ok(())
    })?;
    layer
        .constant
        .for_each(|Constant { g, k }| f.add(&mut out[g as usize], &constants[k as usize]));
    Ok(out)
}
