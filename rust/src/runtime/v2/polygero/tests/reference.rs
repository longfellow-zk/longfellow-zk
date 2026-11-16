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
use crate::{
    core::algebra::AlgebraicField,
    runtime::v2::{
        polygero::{prover_commitment::ColumnOracle, ProverParticipants},
        proto::polygero::PolygeroCommitment,
    },
};

/// Preserve private rows for independent polynomial/forgery checks after prove
/// consumes its input. Duplication is confined to tests; production state is not Clone.
pub(super) fn snapshot<E: Clone>(
    prover: &JointPolygeroProver<(FieldState<E>, ())>,
    ts: &Transcript,
) -> (JointPolygeroProver<(FieldState<E>, ())>, Transcript) {
    // The copy completes on a copy of its session: a fork, whose stamp it takes.
    let mut fork = ts.fork_for_test();
    let session = fork.bound(&()).session();
    let copy = JointPolygeroProver {
        session,
        states: (
            FieldState {
                geom: prover.states.0.geom,
                rows: prover.states.0.rows.clone(),
            },
            (),
        ),
        oracle: ColumnOracle {
            tree: prover.oracle.tree.clone(),
            salts: prover.oracle.salts.clone(),
        },
    };
    (copy, fork)
}

/// Recommitting a wrong witness authenticates successfully but must fail the
/// original linear equations, even with consistently recomputed responses.
pub(super) fn check_recommitted_wrong_witness<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    joint: &JointPolygeroParam<(Participant<'_, W, F, D>, ())>,
    prover: &JointPolygeroProver<(FieldState<F::E>, ())>,
    b: &[F::E],
    a: &[PolygeroLinearTerm<F::E>],
    mut ts: Transcript,
    f: &F,
) {
    let (mut forged, _) = snapshot(prover, &ts);
    let param = &joint.participants.0.param;
    for value in &mut forged.states.0.rows[param.data_start()] {
        f.add(value, &f.one());
    }
    forged.oracle = ColumnOracle::new(param.geom.n, &mut DeterministicRng::new(97), |j, h| {
        joint.participants.append_encoded(&forged.states, j, h)
    });
    let commitment = PolygeroCommitment {
        root: forged.oracle.root(),
    };
    let mut verifier_ts = ts.fork_for_test();
    joint.receive(&commitment, &mut ts.borrow());
    // The forged state completes on the session that received its root.
    forged.session = ts.bound(joint).session();
    let statements = (linear(a, b), ());
    let proof = forged
        .prove(&mut ts.bound(joint), statements.clone())
        .unwrap();
    let verifier = JointPolygeroVerifier::receive(&mut verifier_ts.bound(joint), &commitment);
    let error = verifier
        .reduce(&mut verifier_ts.bound(joint), statements.clone(), &proof)
        .err()
        .unwrap();
    assert_eq!(error.0, "Polygero global arithmetic sum failed");
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
pub(super) fn interpolate<F: AlgebraicField>(nodes: &[F::E], values: &[F::E], f: &F) -> Vec<F::E> {
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
pub(super) fn check<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
    D: crate::runtime::algebra::range_interpolation::EvaluationDomain<W, F>,
>(
    joint: &JointPolygeroParam<(Participant<'_, W, F, D>, ())>,
    prover: &JointPolygeroProver<(FieldState<F::E>, ())>,
    envelope: &JointPolygeroProof<(FieldProof<F::E>, ())>,
    b: &[F::E],
    a: &[PolygeroLinearTerm<F::E>],
    mut ts: Transcript,
    domain: &D,
    f: &F,
) {
    let p = &joint.participants.0.param;
    let proof = &envelope.bodies.0;
    let statements = (linear(a, b), ());
    let commitment = PolygeroCommitment {
        root: prover.oracle.root(),
    };
    let original = ts.fork_for_test();
    let _ = JointPolygeroVerifier::receive(&mut ts.bound(joint), &commitment);
    let g = p.geom;
    let omega: Vec<_> = (0..g.k).map(|i| domain.point(i)).collect();
    let nodes: Vec<_> = p.oracle_range().map(|i| domain.point(i)).collect();
    let challenge = joint.challenges(&statements, &mut ts.borrow()).0;
    let fstar = g.nrow() - 1;
    let rows: Vec<_> = prover
        .states
        .0
        .rows
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let degree = if i == fstar { g.k + g.s } else { g.k };
            interpolate(&nodes[..degree], &row[..degree], f)
        })
        .collect();
    assert_eq!(challenge.batching_samples.len(), fstar);
    let mut h = rows[fstar].clone();
    for (row, values) in rows.iter().enumerate().take(fstar) {
        let samples = &challenge.batching_samples[row];
        // Recover actual coefficients independently on the physical nodes.
        // Treating samples as monomial coefficients would give a different H.
        let batch_nodes: Vec<_> = p
            .oracle_prefix(samples.len())
            .map(|i| domain.point(i))
            .collect();
        let poly = interpolate(&batch_nodes, samples, f);
        add(&mut h, &mul(values, &poly, f), f);
    }
    let mut coefficients = vec![vec![f.zero(); g.k]; g.data_rows()];
    for term in a {
        let width = g.k - g.t;
        f.add(
            &mut coefficients[term.w / width][g.t + term.w % width],
            &f.mulf(&challenge.alpha[term.c], &term.k),
        );
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
    // All committed rows are transmitted in row order at the sampled columns.
    let indices = joint.queries(&envelope.bodies, &mut ts.fork_for_test().borrow());
    assert_eq!(proof.rows.len(), g.nrow() * g.t);
    for row in 0..g.nrow() {
        for (query, &index) in indices.iter().enumerate() {
            assert_eq!(
                proof.rows[row * g.t + query],
                prover.states.0.rows[row][index]
            );
        }
    }
    // Reopen genuine columns after changing the response: authentication must
    // succeed, leaving the global logical sum as the reason for rejection.
    for (logical, expected) in [
        (0, "Polygero arithmetic mask prefix is not zero"),
        (g.t, "Polygero global arithmetic sum failed"),
    ] {
        let h = proof.h.clone();
        let mut z = proof.z.clone();
        let mut changes = vec![f.zero(); g.k];
        changes[logical] = f.one();
        let delta = interpolate(&omega, &changes, f);
        for (sample, i) in z.iter_mut().zip(p.oracle_prefix(2 * g.k)) {
            f.add(sample, &eval(&delta, &domain.point(i), f));
        }
        let mut bodies = (
            FieldProof {
                h,
                z,
                rows: Vec::new(),
            },
            (),
        );
        let mut opening_transcript = ts.fork_for_test();
        let indices = joint.queries(&bodies, &mut opening_transcript.borrow());
        joint
            .participants
            .gather(&prover.states, &mut bodies, &indices);
        let forged = JointPolygeroProof {
            bodies,
            opening: prover.oracle.open(&indices),
        };
        let mut tv = original.fork_for_test();
        let verifier = JointPolygeroVerifier::receive(&mut tv.bound(joint), &commitment);
        let error = verifier
            .reduce(&mut tv.bound(joint), statements.clone(), &forged)
            .err()
            .unwrap();
        assert_eq!(error.0, expected);
    }
    // isolate the column arithmetic and primary response checks.
    for (case, expected) in [
        (0, "Polygero arithmetic check failed"),
        (1, "Polygero primary response check failed"),
    ] {
        let mut h = proof.h.clone();
        let mut z = proof.z.clone();
        if case == 0 {
            for (sample, i) in z.iter_mut().zip(p.oracle_prefix(2 * g.k)) {
                f.add(sample, &eval(&v, &domain.point(i), f));
            }
        } else {
            for sample in h.iter_mut() {
                f.add(sample, &f.one());
            }
        }
        let mut bodies = (
            FieldProof {
                h,
                z,
                rows: Vec::new(),
            },
            (),
        );
        let mut opening_transcript = ts.fork_for_test();
        let indices = joint.queries(&bodies, &mut opening_transcript.borrow());
        joint
            .participants
            .gather(&prover.states, &mut bodies, &indices);
        let forged = JointPolygeroProof {
            bodies,
            opening: prover.oracle.open(&indices),
        };
        let mut tv = original.fork_for_test();
        let verifier = JointPolygeroVerifier::receive(&mut tv.bound(joint), &commitment);
        let error = verifier
            .reduce(&mut tv.bound(joint), statements.clone(), &forged)
            .expect_err("forged Polygero response accepted");
        assert_eq!(error.0, expected);
    }
}
