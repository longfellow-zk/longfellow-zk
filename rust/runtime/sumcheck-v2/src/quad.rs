// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Explicit bindings for the eleven v2 term classes of a v2 layer.
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{
            Constant, ConstantCoordinates, Layer, Linear, LinearCoordinates, Quadratic,
            QuadraticCoordinates,
        },
    },
    runtime::{
        algebra::{blas, RuntimeField},
        sumcheck_v2::monomial,
    },
};

/// Bind quadratic g,l coordinates. Linear terms have no r coordinate and enter
/// the public L(u) correction separately.
pub(super) fn bind_l<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_l: &[F::E],
    f: &F,
) -> Vec<F::E> {
    assert_eq!(
        assertions.len(),
        layer.quadratic_assertions.num_terms() + layer.linear_assertions.num_terms()
    );
    let mut q_r = vec![f.zero(); layer.nw];
    layer.quadratic.for_each(|Quadratic { g, l, r, k }| {
        f.fma(
            &mut q_r[r as usize],
            &f.mulf(&a[g as usize], &constants[k as usize]),
            &b_l[l as usize],
        );
    });
    layer
        .quadratic_one
        .for_each(|QuadraticCoordinates { g, l, r }| {
            f.fma(&mut q_r[r as usize], &a[g as usize], &b_l[l as usize]);
        });
    let mut rho = assertions.iter();
    layer
        .quadratic_minus_one
        .for_each(|QuadraticCoordinates { g, l, r }| {
            f.fnms(&mut q_r[r as usize], &a[g as usize], &b_l[l as usize]);
        });
    layer
        .quadratic_assertions
        .for_each(|QuadraticCoordinates { g: _, l, r }| {
            f.fma(&mut q_r[r as usize], rho.next().unwrap(), &b_l[l as usize]);
        });
    q_r
}

/// Bind quadratic g,r coordinates against W, then add the independent linear
/// classes. Unit terms save a coefficient multiplication; linear assertions add
/// rho directly, without an output weight or a witness multiplication.
#[cfg(any(test, feature = "prover"))]
pub(super) fn bind_r<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    w: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let nq = layer.quadratic_assertions.num_terms();
    assert_eq!(assertions.len(), nq + layer.linear_assertions.num_terms());
    let mut q_l = vec![f.zero(); layer.nw];
    layer.quadratic.for_each(|Quadratic { g, l, r, k }| {
        f.fma(
            &mut q_l[l as usize],
            &f.mulf(&a[g as usize], &constants[k as usize]),
            &w[r as usize],
        );
    });
    layer
        .quadratic_one
        .for_each(|QuadraticCoordinates { g, l, r }| {
            f.fma(&mut q_l[l as usize], &a[g as usize], &w[r as usize]);
        });
    let mut rho = assertions[..nq].iter();
    layer
        .quadratic_minus_one
        .for_each(|QuadraticCoordinates { g, l, r }| {
            f.fnms(&mut q_l[l as usize], &a[g as usize], &w[r as usize]);
        });
    layer
        .quadratic_assertions
        .for_each(|QuadraticCoordinates { g: _, l, r }| {
            f.fma(&mut q_l[l as usize], rho.next().unwrap(), &w[r as usize]);
        });
    add_linear(layer, constants, a, &assertions[nq..], &mut q_l, f);
    q_l
}

#[cfg(any(test, feature = "prover"))]
pub(super) fn add_linear<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    q_l: &mut [F::E],
    f: &F,
) {
    layer.linear.for_each(|Linear { g, l, k }| {
        f.fma(&mut q_l[l as usize], &a[g as usize], &constants[k as usize]);
    });
    layer.linear_one.for_each(|LinearCoordinates { g, l }| {
        f.add(&mut q_l[l as usize], &a[g as usize]);
    });
    assert_eq!(assertions.len(), layer.linear_assertions.num_terms());
    layer
        .linear_minus_one
        .for_each(|LinearCoordinates { g, l }| {
            f.sub(&mut q_l[l as usize], &a[g as usize]);
        });
    let mut rho = assertions.iter();
    layer
        .linear_assertions
        .for_each(|LinearCoordinates { g: _, l }| {
            f.add(&mut q_l[l as usize], rho.next().unwrap());
        });
}

#[cfg(test)]
#[allow(dead_code)]
pub(super) fn weights_next<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point: &[F::E],
    alpha: &F::E,
    f: &F,
) -> Vec<F::E> {
    weights_next_affine(layer, constants, a, assertions, point, alpha, f).0
}

/// a_next = m(u) + alpha*Q(u, .); the next claim subtracts alpha*L(u).
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
    layer.linear.for_each(|Linear { g, l, k }| {
        let (a, m, k) = (&a[g as usize], &weights[l as usize], &constants[k as usize]);
        f.fma(&mut linear, &f.mulf(a, k), m);
    });
    layer.linear_one.for_each(|LinearCoordinates { g, l }| {
        f.fma(&mut linear, &a[g as usize], &weights[l as usize]);
    });
    let nq = layer.quadratic_assertions.num_terms();
    assert_eq!(assertions.len(), nq + layer.linear_assertions.num_terms());
    let mut rho = assertions[nq..].iter();
    layer
        .linear_assertions
        .for_each(|LinearCoordinates { g: _, l }| {
            f.fma(&mut linear, rho.next().unwrap(), &weights[l as usize]);
        });
    let q_r = bind_l(layer, constants, a, assertions, &weights, f);
    layer
        .linear_minus_one
        .for_each(|LinearCoordinates { g, l }| {
            f.fnms(&mut linear, &a[g as usize], &weights[l as usize]);
        });
    blas::axpy(&mut weights, alpha, &q_r, f);
    (weights, linear)
}

pub(super) fn affine_constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer,
    constants: &[F::E],
    a: &[F::E],
    f: &F,
) -> F::E {
    let mut constant = f.zero();
    layer.constant.for_each(|Constant { g, k }| {
        f.fma(&mut constant, &a[g as usize], &constants[k as usize]);
    });
    layer.constant_one.for_each(|ConstantCoordinates { g }| {
        f.add(&mut constant, &a[g as usize]);
    });
    layer
        .constant_minus_one
        .for_each(|ConstantCoordinates { g }| {
            f.sub(&mut constant, &a[g as usize]);
        });
    constant
}
