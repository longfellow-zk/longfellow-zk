// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Explicit arithmetic over the eleven private per-layer streams.
use super::split::{ConstantCoordinates, LinearCoordinates, QuadraticCoordinates, SplitLayer};
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{Constant, Linear, Quadratic},
    },
    runtime::algebra::RuntimeField,
};

/// Bind quadratic g,l coordinates. Linear terms have no r coordinate and enter
/// the public L(u) correction separately.
pub(super) fn bind_l_into<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_l: &[F::E],
    q_r: &mut [F::E],
    f: &F,
) {
    assert_eq!(
        assertions.len(),
        layer.assertion_counts()[0] + layer.assertion_counts()[1]
    );
    assert_eq!(q_r.len(), layer.nw);
    layer
        .quadratic
        .for_each(&layer.quadratic_runs, |Quadratic { g, l, r, k }| {
            f.fma(
                &mut q_r[r as usize],
                &f.mulf(&a[g as usize], &constants[k as usize]),
                &b_l[l as usize],
            );
        });
    layer
        .quadratic_one
        .for_each(&layer.quadratic_runs, |QuadraticCoordinates { g, l, r }| {
            f.fma(&mut q_r[r as usize], &a[g as usize], &b_l[l as usize]);
        });
    let mut rho = assertions.iter();
    layer.quadratic_minus_one.for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g, l, r }| {
            f.fnms(&mut q_r[r as usize], &a[g as usize], &b_l[l as usize]);
        },
    );
    layer.quadratic_assertions.for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g: _, l, r }| {
            f.fma(&mut q_r[r as usize], rho.next().unwrap(), &b_l[l as usize]);
        },
    );
}

/// Bind quadratic g,r coordinates against W, then add the independent linear
/// classes. Unit terms save a coefficient multiplication; linear assertions add
/// rho directly, without an output weight or a witness multiplication.
#[cfg(any(test, feature = "prover"))]
pub(super) fn bind_r_into<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    w: &[F::E],
    q_l: &mut [F::E],
    f: &F,
) {
    let nq = layer.assertion_counts()[0];
    assert_eq!(assertions.len(), nq + layer.assertion_counts()[1]);
    assert_eq!(q_l.len(), layer.nw);
    layer
        .quadratic
        .for_each(&layer.quadratic_runs, |Quadratic { g, l, r, k }| {
            f.fma(
                &mut q_l[l as usize],
                &f.mulf(&a[g as usize], &constants[k as usize]),
                &w[r as usize],
            );
        });
    layer
        .quadratic_one
        .for_each(&layer.quadratic_runs, |QuadraticCoordinates { g, l, r }| {
            f.fma(&mut q_l[l as usize], &a[g as usize], &w[r as usize]);
        });
    let mut rho = assertions[..nq].iter();
    layer.quadratic_minus_one.for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g, l, r }| {
            f.fnms(&mut q_l[l as usize], &a[g as usize], &w[r as usize]);
        },
    );
    layer.quadratic_assertions.for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g: _, l, r }| {
            f.fma(&mut q_l[l as usize], rho.next().unwrap(), &w[r as usize]);
        },
    );
    add_linear(layer, constants, a, &assertions[nq..], q_l, f);
}

#[cfg(any(test, feature = "prover"))]
fn add_linear<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    q_l: &mut [F::E],
    f: &F,
) {
    layer
        .linear
        .for_each(&layer.linear_runs, |Linear { g, l, k }| {
            f.fma(&mut q_l[l as usize], &a[g as usize], &constants[k as usize]);
        });
    layer
        .linear_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.add(&mut q_l[l as usize], &a[g as usize]);
        });
    assert_eq!(assertions.len(), layer.assertion_counts()[1]);
    layer
        .linear_minus_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.sub(&mut q_l[l as usize], &a[g as usize]);
        });
    let mut rho = assertions.iter();
    layer
        .linear_assertions
        .for_each(&layer.linear_runs, |LinearCoordinates { g: _, l }| {
            f.add(&mut q_l[l as usize], rho.next().unwrap());
        });
}

/// Contract the linear stream at the same global monomial weights used by Q.
/// The caller sums fragment corrections and subtracts alpha*L(u) from the
/// ordinary two-factor transition. Purely linear fragments use this same path.
pub(super) fn affine_linear<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    weights: &[F::E],
    f: &F,
) -> F::E {
    let mut linear = f.zero();
    layer
        .linear
        .for_each(&layer.linear_runs, |Linear { g, l, k }| {
            let (a, m, k) = (&a[g as usize], &weights[l as usize], &constants[k as usize]);
            f.fma(&mut linear, &f.mulf(a, k), m);
        });
    layer
        .linear_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.fma(&mut linear, &a[g as usize], &weights[l as usize]);
        });
    let nq = layer.assertion_counts()[0];
    assert_eq!(assertions.len(), nq + layer.assertion_counts()[1]);
    let mut rho = assertions[nq..].iter();
    layer
        .linear_assertions
        .for_each(&layer.linear_runs, |LinearCoordinates { g: _, l }| {
            f.fma(&mut linear, rho.next().unwrap(), &weights[l as usize]);
        });
    layer
        .linear_minus_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.fnms(&mut linear, &a[g as usize], &weights[l as usize]);
        });
    linear
}

pub(super) fn affine_constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    f: &F,
) -> F::E {
    let mut constant = f.zero();
    layer
        .constant
        .for_each(&layer.constant_runs, |Constant { g, k }| {
            f.fma(&mut constant, &a[g as usize], &constants[k as usize]);
        });
    layer
        .constant_one
        .for_each(&layer.constant_runs, |ConstantCoordinates { g }| {
            f.add(&mut constant, &a[g as usize]);
        });
    layer
        .constant_minus_one
        .for_each(&layer.constant_runs, |ConstantCoordinates { g }| {
            f.sub(&mut constant, &a[g as usize]);
        });
    constant
}

#[cfg(test)]
#[path = "../tests/quad_fixtures.rs"]
mod fixtures;
#[cfg(test)]
pub(super) use fixtures::{bind_l, bind_r, weights_next_affine};
