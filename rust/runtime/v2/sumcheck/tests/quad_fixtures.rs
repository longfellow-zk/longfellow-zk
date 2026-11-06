// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub(crate) fn bind_l<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut q = vec![f.zero(); layer.nw];
    bind_l_into(layer, constants, a, assertions, b, &mut q, f);
    q
}
pub(crate) fn bind_r<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    w: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut q = vec![f.zero(); layer.nw];
    bind_r_into(layer, constants, a, assertions, w, &mut q, f);
    q
}
pub(crate) fn weights_next_affine<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point: &[F::E],
    alpha: &F::E,
    f: &F,
) -> (Vec<F::E>, F::E) {
    let mut m = crate::runtime::v2::sumcheck::monomial::weights(
        crate::util::ceil_log2(layer.nw),
        layer.nw,
        point,
        f,
    );
    let q = bind_l(layer, constants, a, assertions, &m, f);
    let linear = affine_linear(layer, constants, a, assertions, &m, f);
    crate::runtime::algebra::blas::axpy(&mut m, alpha, &q, f);
    (m, linear)
}
