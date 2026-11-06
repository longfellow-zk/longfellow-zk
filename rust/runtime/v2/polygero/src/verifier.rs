// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Authenticate the shared columns, then check each field's equations.
use sha2::Digest as _;

use super::{
    constraints, ensure, hash, joint::*, PolygeroCommitment, PolygeroError, PolygeroParam,
};
use crate::runtime::{
    algebra::{
        blas, range_interpolation::interpolate_range, EvaluationDomain, InterpolationPlan,
        RuntimeField,
    },
    proto::Digest,
    v2::transcript::Transcript,
};
#[cfg(any(test, feature = "verifier"))]
pub struct JointPolygeroVerifier<L: Participants> {
    param: JointPolygeroParam<L>,
    commitment: Option<PolygeroCommitment>,
}
#[cfg(any(test, feature = "verifier"))]
impl<L: Participants> JointPolygeroVerifier<L> {
    pub fn new(param: JointPolygeroParam<L>) -> Self {
        Self {
            param,
            commitment: None,
        }
    }
    pub fn from_received(
        param: JointPolygeroParam<L>,
        received: &ReceivedCommitment,
    ) -> Result<Self, PolygeroError> {
        ensure(
            param.context == received._context,
            "joint received context mismatch",
        )?;
        Ok(Self {
            param,
            commitment: Some(received._root.clone()),
        })
    }
    pub fn receive_commitment(&mut self, root: &PolygeroCommitment, t: &mut Transcript) {
        self.param.receive(root, t);
        self.commitment = Some(root.clone());
    }
    /// Complete standalone verification, including the mandatory final seal.
    pub fn verify(
        &self,
        root: &PolygeroCommitment,
        proof: crate::runtime::v2::transcript::Unverified<'_, JointPolygeroProof<L::Bodies>>,
        s: &L::Statements,
        mut transcript: Transcript,
    ) -> Result<crate::runtime::v2::transcript::VerifiedProof, PolygeroError> {
        self.reduce(root, &proof, s, &mut transcript)?;
        proof
            .checked(transcript)
            .map_err(|e| PolygeroError(e.into()))
    }
    pub(crate) fn reduce(
        &self,
        root: &PolygeroCommitment,
        proof: &JointPolygeroProof<L::Bodies>,
        s: &L::Statements,
        t: &mut Transcript,
    ) -> Result<(), PolygeroError> {
        let p = &self.param;
        ensure(proof.context == p.context, "joint proof context mismatch")?;
        ensure(
            self.commitment.as_ref() == Some(root),
            "joint commitment was not received",
        )?;
        p.participants.validate_statements(s)?;
        p.participants.validate_bodies(&proof.bodies)?;
        crate::runtime::v2::proto::polygero::validate_opening(
            &proof.opening,
            p.config.t,
            p.config.n,
        )?;
        let c = p.challenges(s, t);
        let indices = p.queries(&proof.bodies, t);
        let leaves: Vec<_> = indices
            .iter()
            .enumerate()
            .map(|(q, &j)| {
                let mut h = hash::leaf(&p.context, j, &proof.opening.nonce[q]);
                p.participants
                    .append_opened(&proof.bodies, q, p.config.t, &mut h);
                (
                    j,
                    Digest {
                        data: h.finalize().into(),
                    },
                )
            })
            .collect();
        crate::runtime::merkle::heap::verify_proof_with_hash(
            p.config.n,
            &root.root,
            &proof.opening.path,
            &leaves,
            |l, r| hash::node(&p.context, l, r),
        )
        .map_err(|e| PolygeroError(e.to_string()))?;
        // The one opening authenticates every field's column values. Each field
        // still needs its own low-degree and affine-equation checks.
        p.participants.check(&proof.bodies, s, &c, &indices)
    }
}
#[cfg(any(test, feature = "verifier"))]
pub(super) fn verify_primary_response<
    const W: usize,
    F: RuntimeField<W>,
    D: EvaluationDomain<W, F>,
>(
    param: &PolygeroParam,
    response: &[F::E],
    indices: &[usize],
    batching_samples: &[Vec<F::E>],
    opened: &[F::E],
    domain: &D,
    f: &F,
) -> Result<(), PolygeroError> {
    let g = param.geom;
    let mut expected = opened_row(param, opened, param.fstar_row()).to_vec();
    let encoder = domain.make_range(param.oracle_prefix(g.s + 1), param.oracle_range());
    for row in param.batched_rows() {
        let extended = encoder.apply(&batching_samples[row]);
        let coefficients = blas::gather(indices, &extended);
        let w = opened_row(param, opened, row);
        blas::vaxpy(&mut expected, &coefficients, w, f);
    }
    let h = interpolate_range(g.k, response, param.oracle_range(), domain);
    ensure(
        blas::gather(indices, &h) == expected,
        "Polygero primary response check failed",
    )
}

#[cfg(any(test, feature = "verifier"))]
pub(super) fn verify_arithmetic<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
    param: &PolygeroParam,
    response: &[F::E],
    indices: &[usize],
    rows: &[Vec<F::E>],
    opened: &[F::E],
    tau: &F::E,
    domain: &D,
    f: &F,
) -> Result<(), PolygeroError> {
    let g = param.geom;
    let z = interpolate_range(g.k, response, 0..g.k + g.n, domain);
    let sum = f.addf(&blas::dot1(&z[g.t..g.k], f), tau);
    ensure(f.is_zero(&sum), "Polygero global arithmetic sum failed")?;
    let actual = blas::gather(indices, &z[g.k..]);
    let mut expected = constraint_sum(param, rows, indices, opened, domain, f);
    let vanishing = blas::gather(indices, &super::polynomials::vanishing(&g, domain, f));
    let u = opened_row(param, opened, param.u_row());
    blas::vaxpy(&mut expected, &vanishing, u, f);
    let selector = blas::gather(indices, &super::polynomials::selector(&g, domain, f));
    let m = opened_row(param, opened, param.m_row());
    blas::vaxpy(&mut expected, &selector, m, f);
    ensure(actual == expected, "Polygero arithmetic check failed")
}

#[cfg(any(test, feature = "verifier"))]
pub(super) fn constraint_sum<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
    param: &PolygeroParam,
    rows: &[Vec<F::E>],
    indices: &[usize],
    opened: &[F::E],
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    let g = param.geom;
    let encoder = domain.make_range(0..g.k, param.oracle_range());
    let mut sum = vec![f.zero(); indices.len()];
    for row in 0..rows.len() {
        let extended = encoder.apply(&rows[row]);
        let row_values = blas::gather(indices, &extended);
        let w = opened_row(param, opened, param.data_start() + row);
        blas::vaxpy(&mut sum, &row_values, w, f);
    }
    sum
}

#[cfg(any(test, feature = "verifier"))]
pub(super) fn opened_row<'a, E>(param: &PolygeroParam, rows: &'a [E], row: usize) -> &'a [E] {
    let t = param.geom.t;
    &rows[row * t..(row + 1) * t]
}

/// Check one participant using the common opening positions and its own field.
pub(super) fn check_response<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
    param: &PolygeroParam,
    body: &FieldProof<F::E>,
    statement: &LinearStatement<F::E>,
    challenge: &FieldChallenges<F::E>,
    indices: &[usize],
    domain: &D,
    f: &F,
) -> Result<(), PolygeroError> {
    verify_primary_response(
        param,
        &body.h,
        indices,
        &challenge.batching_samples,
        &body.rows,
        domain,
        f,
    )?;
    let rows =
        constraints::batch_constraints(param, &statement.b, &statement.a, &challenge.alpha, f);
    let tau = blas::dot(&challenge.alpha, &statement.b, f);
    verify_arithmetic(param, &body.z, indices, &rows, &body.rows, &tau, domain, f)?;
    // Avoid retaining one dense matrix per participant during recursion.
    drop(rows);
    Ok(())
}
