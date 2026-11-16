// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Authenticate the shared columns, then check each field's equations.
use core::marker::PhantomData;

use sha2::Digest as _;

use super::{constraints, ensure, hash, joint::*, PolygeroError, PolygeroParam};
#[cfg(any(test, feature = "testonly"))]
use crate::runtime::v2::transcript::{Transcript, Unverified, VerifiedProof};
use crate::runtime::{
    algebra::{
        blas,
        range_interpolation::{interpolate_range, EvaluationDomain, InterpolationPlan},
        RuntimeField,
    },
    v2::{
        merkle::verify_proof,
        proto::{
            polygero::{validate_opening, FieldProof, JointPolygeroProof, PolygeroCommitment},
            Digest,
        },
        transcript::{Bound, SessionStamp},
    },
};
/// Verifier state between the commitment and the opening. It records the
/// session that received the commitment and checks only on that session.
#[cfg(any(test, feature = "verifier"))]
#[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
pub struct JointPolygeroVerifier<L: Participants> {
    session: SessionStamp,
    commitment: PolygeroCommitment,
    _participants: PhantomData<fn() -> L>,
}
#[cfg(any(test, feature = "verifier"))]
impl<L: Participants> JointPolygeroVerifier<L> {
    /// Receive the root on `t`'s session.
    pub(crate) fn receive(
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        root: &PolygeroCommitment,
    ) -> Self {
        let param = t.part();
        param.receive(root, &mut t.transcript());
        Self {
            session: t.session(),
            commitment: root.clone(),
            _participants: PhantomData,
        }
    }
    /// `receive` on a bare session, for tests and benchmarks outside the
    /// crate (`Transcript::bound_for_test`).
    #[cfg(feature = "testonly")]
    pub fn receive_for_test(
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        root: &PolygeroCommitment,
    ) -> Self {
        Self::receive(t, root)
    }
    /// Complete standalone verification of a bare body (`JointPolygeroParam::read`)
    /// on the session that received the commitment, including the mandatory
    /// final seal, against `statements`. For tests and tools only: complete
    /// proofs run `reduce` inside their own composition and check their own
    /// seal.
    #[cfg(any(test, feature = "testonly"))]
    pub fn verify(
        self,
        mut transcript: Transcript,
        param: &JointPolygeroParam<L>,
        statements: L::Statements,
        proof: Unverified<'_, JointPolygeroProof<L::Bodies>>,
    ) -> Result<VerifiedProof, PolygeroError> {
        self.reduce(&mut transcript.bound(param), statements, &proof)?;
        transcript
            .check_seal(proof)
            .map_err(|e| PolygeroError(e.into()))
    }
    /// Check the opening on the session that received the commitment against
    /// `statements`, the equations of every field. It draws the batching
    /// weights at the current boundary, which must follow the last message
    /// any statement depends on, and consumes them (transcript I8). This is
    /// not complete verification: the caller still checks the seal.
    pub(crate) fn reduce(
        self,
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        statements: L::Statements,
        proof: &JointPolygeroProof<L::Bodies>,
    ) -> Result<(), PolygeroError> {
        ensure(
            self.session == t.session(),
            "joint verifier session mismatch",
        )?;
        let p = t.part();
        p.participants.validate_bodies(&proof.bodies)?;
        validate_opening(&proof.opening, p.config.t, p.config.n)?;
        p.participants.validate_statements(&statements)?;
        let weights = p.weights_for(&statements, &mut t.transcript());
        let indices = p.queries(&proof.bodies, &mut t.transcript());
        let leaves: Vec<_> = indices
            .iter()
            .enumerate()
            .map(|(q, &j)| {
                let mut h = hash::leaf(j, &proof.opening.nonce[q]);
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
        verify_proof(
            p.config.n,
            &self.commitment.root,
            &proof.opening.path,
            &leaves,
        )
        .map_err(|e| PolygeroError(e.to_string()))?;
        // The one opening authenticates every field's column values. Each field
        // still needs its own low-degree and affine-equation checks.
        p.participants
            .check(&proof.bodies, &statements, &weights, &indices)?;
        Ok(())
    }
}
#[cfg(any(test, feature = "verifier"))]
fn verify_primary_response<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
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
fn verify_arithmetic<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
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
    ensure(
        blas::equal0(&z[..g.t], f),
        "Polygero arithmetic mask prefix is not zero",
    )?;
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
fn constraint_sum<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
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
    for (row, values) in rows.iter().enumerate() {
        let extended = encoder.apply(values);
        let row_values = blas::gather(indices, &extended);
        let w = opened_row(param, opened, param.data_start() + row);
        blas::vaxpy(&mut sum, &row_values, w, f);
    }
    sum
}

#[cfg(any(test, feature = "verifier"))]
fn opened_row<'a, E>(param: &PolygeroParam, rows: &'a [E], row: usize) -> &'a [E] {
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
