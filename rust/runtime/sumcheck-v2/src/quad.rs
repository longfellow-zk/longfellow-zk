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

//! Form dense coefficient arrays by binding a sparse circuit tensor.
//!
//! In QUAD[g,l,r], g indexes layer outputs and l,r index its input wires.
//! Both routines bind g with the weights a[g]. `bind_l` also binds l with b_l[l],
//! leaving q_r[r]; `bind_r` binds r with b_r[r], leaving q_l[l]. The protocol uses
//! b_l = m_l, the monomial weights at the sampled point, and b_r = W, the witness.
//!
//! A zero coefficient marks an assertion quad. Its sampled assertion coefficient
//! replaces the entire a[g]*QUAD[g,l,r] factor. Both bindings consume the same
//! assertion sequence in circuit traversal order.
use crate::{
    core::proto::{Layer, SerializableField},
    runtime::{
        algebra::{blas, RuntimeField},
        sumcheck_v2::monomial,
    },
};

/// Bind g,l with a,b_l, leaving r free:
/// `q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] b_l[l]`.
/// Both parties use b_l[l] = m_l[l] = product_j u[j]^l_j at the sampled point u.
pub(super) fn bind_l<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_l: &[F::E],
    f: &F,
) -> Vec<F::E> {
    if layer.coefficients().is_some() {
        return bind_partition::<W, F, true>(layer, constants, a, assertions, b_l, f);
    }
    let mut q_r = vec![f.zero(); layer.nw()];
    let one = f.one();
    let mut assertion_challenges = assertions.iter();
    layer.for_each_term(constants, |term| {
        let g = term.g as usize;
        let coefficient = if f.is_zero(&term.k) {
            assertion_challenges
                .next()
                .expect("missing assertion challenge")
                .clone()
        } else if term.k == one {
            a[g].clone()
        } else {
            f.mulf(&a[g], &term.k)
        };
        let l = term.h0 as usize;
        let r = term.h1 as usize;
        f.fma(&mut q_r[r], &coefficient, &b_l[l]);
    });
    assert!(
        assertion_challenges.next().is_none(),
        "unused assertion challenge"
    );
    q_r
}

/// Bind g,r with a,b_r, leaving l free:
/// `q_l[l] = sum_{g,r} a[g] QUAD[g,l,r] b_r[r]`.
/// The prover uses b_r[r] = W[r], the layer's input witness.
#[cfg(any(test, feature = "prover"))]
pub(super) fn bind_r<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_r: &[F::E],
    f: &F,
) -> Vec<F::E> {
    if layer.coefficients().is_some() {
        let mut q = bind_partition::<W, F, false>(layer, constants, a, assertions, b_r, f);
        add_linear(
            layer,
            constants,
            a,
            &assertions[layer.coefficients().unwrap().assertions.num_terms()..],
            &mut q,
            f,
        );
        return q;
    }
    let mut q_l = vec![f.zero(); layer.nw()];
    let one = f.one();
    let mut assertion_challenges = assertions.iter();
    layer.for_each_term(constants, |term| {
        let g = term.g as usize;
        let coefficient = if f.is_zero(&term.k) {
            // Replace each assertion marker's zero coefficient by its own
            // challenge, in quad order. Both bindings reuse this sequence.
            assertion_challenges
                .next()
                .expect("missing assertion challenge")
                .clone()
        } else if term.k == one {
            a[g].clone()
        } else {
            f.mulf(&a[g], &term.k)
        };
        let l = term.h0 as usize;
        let r = term.h1 as usize;
        f.fma(&mut q_l[l], &coefficient, &b_r[r]);
    });
    assert!(
        assertion_challenges.next().is_none(),
        "unused assertion challenge"
    );
    if let Some([linear, _]) = layer.affine() {
        let mone = f.mone();
        linear.for_each_term(constants, |t| {
            let output = &mut q_l[t.h0 as usize];
            if t.k == one {
                f.add(output, &a[t.g as usize]);
            } else if t.k == mone {
                f.sub(output, &a[t.g as usize]);
            } else {
                f.fma(output, &a[t.g as usize], &t.k);
            }
        });
    }
    q_l
}

/// Express A + alpha*B as weights on the layer's input wires:
///
/// ```text
/// m_l[l] = product_j point_l[j]^l_j,
/// q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] m_l[l],
/// a_next[r] = m_l[r] + alpha*q_r[r].
/// ```
///
/// Thus sum_r a_next[r]*W[r] = A + alpha*B. Prover and verifier use the same
/// public computation; only bind_r, above, needs the prover's witness.
#[cfg(test)]
#[allow(dead_code)] // Reference entry point for independent wiring diagnostics.
pub(super) fn weights_next<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point_l: &[F::E],
    alpha: &F::E,
    f: &F,
) -> Vec<F::E> {
    weights_next_affine(layer, constants, a, assertions, point_l, alpha, f).0
}

pub(super) fn weights_next_affine<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point: &[F::E],
    alpha: &F::E,
    f: &F,
) -> (Vec<F::E>, F::E, F::E) {
    let mut weights = monomial::weights(layer.logw(), layer.nw(), point, f);
    let mut linear = f.zero();
    if let Some([stream, _]) = layer.affine() {
        let one = f.one();
        let mone = f.mone();
        stream.for_each_general_term(constants, |t| {
            let a = &a[t.g as usize];
            let m = &weights[t.h0 as usize];
            if t.k == one {
                f.fma(&mut linear, a, m);
            } else if t.k == mone {
                f.fnms(&mut linear, a, m);
            } else {
                f.fma(&mut linear, &f.mulf(a, &t.k), m);
            }
        });
    }
    if let Some([stream, _]) = layer.affine() {
        if let Some(c) = stream.coefficients() {
            c.units
                .for_each(|g, l, _| f.fma(&mut linear, &a[g as usize], &weights[l as usize]));
        }
    }
    if let Some([s, _]) = layer.affine() {
        if let Some(c) = s.coefficients() {
            let qn = layer.coefficients().unwrap().assertions.num_terms();
            let mut rho = assertions[qn..].iter();
            c.assertions
                .for_each(|_, l, _| f.fma(&mut linear, rho.next().unwrap(), &weights[l as usize]));
            assert!(rho.next().is_none());
        }
    }
    let q = bind_l(layer, constants, a, assertions, &weights, f);
    blas::axpy(&mut weights, alpha, &q, f);
    (weights, affine_constant(layer, constants, a, f), linear)
}

pub(super) fn affine_constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    f: &F,
) -> F::E {
    let mut result = f.zero();
    if let Some([_, stream]) = layer.affine() {
        stream.for_each_general_term(constants, |t| f.fma(&mut result, &a[t.g as usize], &t.k));
        if let Some(c) = stream.coefficients() {
            c.units
                .for_each(|g, _, _| f.add(&mut result, &a[g as usize]));
        }
    }
    result
}

/// The coefficient class is chosen once per array, outside its hot loop.
fn bind_partition<const W: usize, F: RuntimeField<W> + SerializableField, const LEFT: bool>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut q = vec![f.zero(); layer.nw()];
    let c = layer.coefficients().unwrap();
    layer.for_each_general_term(constants, |t| {
        let (l, r) = (t.h0 as usize, t.h1 as usize);
        let (target, source) = if LEFT { (r, l) } else { (l, r) };
        f.fma(&mut q[target], &f.mulf(&a[t.g as usize], &t.k), &b[source]);
    });
    c.units.for_each(|g, l, r| {
        let (target, source) = if LEFT { (r, l) } else { (l, r) };
        f.fma(&mut q[target as usize], &a[g as usize], &b[source as usize]);
    });
    assert_eq!(
        assertions.len(),
        c.assertions.num_terms() + layer.linear_assertion_count(),
        "assertion shape mismatch"
    );
    let mut coefficients = assertions.iter();
    c.assertions.for_each(|_, l, r| {
        let (target, source) = if LEFT { (r, l) } else { (l, r) };
        f.fma(
            &mut q[target as usize],
            coefficients.next().unwrap(),
            &b[source as usize],
        );
    });
    q
}
#[cfg(any(test, feature = "prover"))]
fn add_linear<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    q: &mut [F::E],
    f: &F,
) {
    if let Some([s, _]) = layer.affine() {
        let mone = f.mone();
        s.for_each_general_term(constants, |t| {
            if t.k == mone {
                f.sub(&mut q[t.h0 as usize], &a[t.g as usize]);
            } else {
                f.fma(&mut q[t.h0 as usize], &a[t.g as usize], &t.k);
            }
        });
        if let Some(c) = s.coefficients() {
            assert_eq!(assertions.len(), c.assertions.num_terms());
            let mut rho = assertions.iter();
            c.assertions
                .for_each(|_, l, _| f.add(&mut q[l as usize], rho.next().unwrap()));
            c.units
                .for_each(|g, l, _| f.add(&mut q[l as usize], &a[g as usize]));
        }
    }
}
