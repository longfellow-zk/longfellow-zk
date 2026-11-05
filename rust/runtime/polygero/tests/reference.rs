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

//! Independent coefficient arithmetic, kept entirely outside production code.
use super::*;
use crate::{core::algebra::AlgebraicField, runtime::proto::Digest};

/// Preserve private rows for independent polynomial/forgery checks after prove
/// consumes its input. Duplication is confined to tests; production state is not Clone.
pub(in crate::runtime::polygero) fn snapshot<const W: usize, F: RuntimeField<W>>(
    prover: &PolygeroProver<W, F>,
) -> PolygeroProver<W, F> {
    PolygeroProver {
        param: prover.param.clone(),
        w: prover.w.clone(),
        tree: MerkleHeap {
            num_leaves: prover.tree.num_leaves,
            layers: prover.tree.layers.clone(),
        },
        salts: prover.salts.clone(),
    }
}

/// A commitment to an incorrect virtual output must fail authentication, even
/// when the prover computes both responses from that same incorrect full W.
pub(in crate::runtime::polygero) fn check_virtual_product_binding<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    prover: &PolygeroProver<W, F>,
    b: &[F::E],
    a: &[PolygeroLinearTerm<F::E>],
    statement: &Digest,
    mut ts: Transcript,
    domain: &D,
    f: &F,
) {
    let mut forged = snapshot(prover);
    let param = forged.param.clone();
    let output = param.data_start() + param.geom.ordinary_rows() + 2;
    for value in &mut forged.w[output] {
        f.add(value, &f.one());
    }
    let leaves: Vec<_> = (0..param.geom.n)
        .map(|j| {
            super::super::hash::leaf(
                &param.context,
                j,
                forged.w.iter().map(|row| &row[j]),
                &forged.salts[j],
                f,
            )
        })
        .collect();
    forged.tree = MerkleHeap::new_with_hash(&leaves, |l, r| {
        super::super::hash::node(&param.context, l, r)
    });
    let commitment = PolygeroCommitment {
        root: forged.tree.root(),
    };
    let mut verifier_ts = ts.clone();
    transcript::receive_commitment(&mut ts, &param, &commitment);
    let proof = forged.prove(b, &mut ts, a, statement, domain, f).unwrap();
    let mut verifier = super::super::PolygeroVerifier::new(param);
    verifier.receive_commitment(&commitment, &mut verifier_ts);
    let error = verifier
        .verify(
            b,
            &commitment,
            &proof,
            a,
            statement,
            &mut verifier_ts,
            domain,
            f,
        )
        .unwrap_err();
    assert!(error.0.starts_with("root mismatch:"), "{error}");
}

fn add<F: AlgebraicField>(a: &mut Vec<F::E>, b: &[F::E], f: &F) {
    a.resize(a.len().max(b.len()), f.zero());
    for (x, y) in a.iter_mut().zip(b) {
        f.add(x, y);
    }
}
fn scale<F: AlgebraicField>(a: &[F::E], x: &F::E, f: &F) -> Vec<F::E> {
    a.iter().map(|y| f.mulf(x, y)).collect()
}
fn mul<F: AlgebraicField>(a: &[F::E], b: &[F::E], f: &F) -> Vec<F::E> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut out = vec![f.zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            f.add(&mut out[i + j], &f.mulf(x, y));
        }
    }
    out
}
fn eval<F: AlgebraicField>(p: &[F::E], x: &F::E, f: &F) -> F::E {
    p.iter()
        .rev()
        .fold(f.zero(), |acc, c| f.addf(c, &f.mulf(&acc, x)))
}
fn trim<F: AlgebraicField>(p: &mut Vec<F::E>, f: &F) {
    while p.last().is_some_and(|x| f.is_zero(x)) {
        p.pop();
    }
}
pub(in crate::runtime::polygero) fn interpolate<F: AlgebraicField>(
    nodes: &[F::E],
    values: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut out = vec![];
    for (i, x) in nodes.iter().enumerate() {
        let mut basis = vec![f.one()];
        let mut denominator = f.one();
        for (j, y) in nodes.iter().enumerate() {
            if i != j {
                basis = mul(&basis, &[f.neg(y), f.one()], f);
                f.mul(&mut denominator, &f.subf(x, y));
            }
        }
        add(
            &mut out,
            &scale(&basis, &f.mulf(&values[i], &f.invert(&denominator)), f),
            f,
        );
    }
    trim(&mut out, f);
    out
}
fn vanish<F: AlgebraicField>(nodes: &[F::E], f: &F) -> Vec<F::E> {
    nodes
        .iter()
        .fold(vec![f.one()], |acc, x| mul(&acc, &[f.neg(x), f.one()], f))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::runtime::polygero) fn check<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: crate::runtime::algebra::EvaluationDomain<W, F>,
>(
    prover: &PolygeroProver<W, F>,
    proof: &PolygeroProof<F::E>,
    b: &[F::E],
    a: &[PolygeroLinearTerm<F::E>],
    statement: &Digest,
    mut ts: Transcript,
    domain: &D,
    f: &F,
) {
    let p = &prover.param;
    let commitment = PolygeroCommitment {
        root: prover.tree.root(),
    };
    let mut verifier = super::super::PolygeroVerifier::new(p.clone());
    verifier.receive_commitment(&commitment, &mut ts);
    let mut verifier_ts = ts.clone();
    let g = p.geom;
    let omega: Vec<_> = (0..g.k).map(|i| domain.point(i)).collect();
    let nodes: Vec<_> = p.oracle_range().map(|i| domain.point(i)).collect();
    let challenge = transcript::challenges(&mut ts, p, b.len(), statement, f);
    let fstar = g.nrow() - 1;
    let rows: Vec<_> = prover
        .w
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let degree = if i == fstar { g.k + g.s } else { g.k };
            interpolate(&nodes[..degree], &row[..degree], f)
        })
        .collect();
    assert_eq!(challenge.batching_samples.len(), fstar);
    let mut h = rows[fstar].clone();
    for row in 0..fstar {
        let samples = &challenge.batching_samples[row];
        // Recover actual coefficients independently on the physical nodes.
        // Treating samples as monomial coefficients would give a different H.
        let batch_nodes: Vec<_> = p
            .oracle_prefix(samples.len())
            .map(|i| domain.point(i))
            .collect();
        let poly = interpolate(&batch_nodes, samples, f);
        add(&mut h, &mul(&rows[row], &poly, f), f);
    }
    let mut coefficients = vec![vec![f.zero(); g.k]; g.data_rows()];
    for term in a {
        let width = g.k - g.t;
        f.add(
            &mut coefficients[term.w / width][g.t + term.w % width],
            &f.mulf(&challenge.alpha[term.c], &term.k),
        );
    }
    for (i, product) in p.products.iter().enumerate() {
        for (part, w) in [product.x, product.y, product.z].into_iter().enumerate() {
            let weight = &challenge.alpha[b.len() + 3 * i + part];
            let width = g.k.div_ceil(2) - g.t;
            f.add(
                &mut coefficients[g.ordinary_rows() + 3 * (i / width) + part][g.t + i % width],
                weight,
            );
            let ordinary_width = g.k - g.t;
            f.sub(
                &mut coefficients[w / ordinary_width][g.t + w % ordinary_width],
                weight,
            );
        }
    }
    let v = vanish(&omega, f);
    let selector: Vec<_> = (0..g.k)
        .map(|i| if i < g.t { f.zero() } else { f.one() })
        .collect();
    let z = interpolate(&omega, &selector, f);
    let mut n = mul(&v, &rows[0], f);
    add(&mut n, &mul(&z, &rows[1], f), f);
    for row in 0..coefficients.len() {
        let c_poly = interpolate(&omega, &coefficients[row], f);
        add(&mut n, &mul(&rows[2 + row], &c_poly, f), f);
    }
    assert!(h.len() <= g.k + g.s && n.len() <= 2 * g.k);
    let tau = challenge
        .alpha
        .iter()
        .zip(b)
        .fold(f.zero(), |acc, (weight, value)| {
            f.subf(&acc, &f.mulf(weight, value))
        });
    let sum = omega[g.t..]
        .iter()
        .fold(f.zero(), |acc, x| f.addf(&acc, &eval(&n, x, f)));
    assert_eq!(sum, tau);
    assert_eq!(
        proof.h,
        p.oracle_prefix(proof.h.len())
            .map(|i| eval(&h, &domain.point(i), f))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        proof.z,
        p.oracle_prefix(proof.z.len())
            .map(|i| eval(&n, &domain.point(i), f))
            .collect::<Vec<_>>()
    );
    // Check the packed-row layout against W independently of open_columns.
    // Product outputs remain in the commitment but are absent from the proof.
    let indices = transcript::queries(&mut ts.clone(), p, &proof.h, &proof.z, f);
    let product_start = 2 + g.ordinary_rows();
    let mut sent_rows: Vec<_> = (0..product_start).collect();
    for group in 0..g.product_groups() {
        sent_rows.push(product_start + 3 * group);
        sent_rows.push(product_start + 3 * group + 1);
    }
    sent_rows.push(fstar);
    assert_eq!(proof.rows.len(), (g.nrow() - g.product_groups()) * g.t);
    for i in 0..sent_rows.len() {
        let row = sent_rows[i];
        for query in 0..indices.len() {
            assert_eq!(proof.rows[i * g.t + query], prover.w[row][indices[query]]);
        }
    }
    // Derive each virtual product value independently at the queried columns.
    for group in 0..g.product_groups() {
        let start = (product_start + 2 * group) * g.t;
        let pair = &proof.rows[start..start + 2 * g.t];
        for query in 0..indices.len() {
            assert_eq!(
                f.mulf(&pair[query], &pair[g.t + query]),
                prover.w[product_start + 3 * group + 2][indices[query]],
            );
        }
    }
    // Reopen genuine columns after changing the response: authentication must
    // succeed, leaving the global logical sum as the reason for rejection.
    let h = proof.h.clone();
    let mut z = proof.z.clone();
    let mut changes = vec![f.zero(); g.k];
    changes[g.t] = f.one();
    let delta = interpolate(&omega, &changes, f);
    for (sample, i) in z.iter_mut().zip(p.oracle_prefix(2 * g.k)) {
        f.add(sample, &eval(&delta, &domain.point(i), f));
    }
    let indices = transcript::queries(&mut ts, p, &h, &z, f);
    let (rows, opening) = prover.open_columns(&indices);
    let forged = PolygeroProof {
        h,
        z,
        rows,
        opening,
    };
    let error = verifier
        .verify(
            b,
            &commitment,
            &forged,
            a,
            statement,
            &mut verifier_ts,
            domain,
            f,
        )
        .unwrap_err();
    assert_eq!(error.0, "Polygero global arithmetic sum failed");
}
