// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Commitment and responses for a typed list of fields.
use super::{
    constraints, ensure, joint::*, prover_commitment::ColumnOracle, PolygeroError, PolygeroParam,
    ProverParticipants,
};
use crate::runtime::{
    algebra::{
        blas,
        range_interpolation::{EvaluationDomain, InterpolationPlan},
        RuntimeField,
    },
    random::PrivateRandom,
    v2::{
        proto::polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroGeometry},
        transcript::{Bound, SessionStamp},
    },
};
/// One field's encoded rows and the geometry they were encoded for. Opening
/// compares the geometry with the parameter's, so rows committed for another
/// parameter of the same row count and width are rejected.
#[doc(hidden)]
pub struct FieldState<E> {
    pub(super) geom: PolygeroGeometry,
    pub(super) rows: Vec<Vec<E>>,
}
/// Prover state between the commitment and the opening. It records the
/// session that received its commitment and opens only on that session.
#[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
pub struct JointPolygeroProver<S> {
    pub(super) session: SessionStamp,
    pub(super) states: S,
    pub(super) oracle: ColumnOracle,
}
impl<S> JointPolygeroProver<S> {
    /// Commit the witnesses and send the root on `t`'s session. The state
    /// keeps only the encoded rows, never the witnesses, which the caller
    /// still owns.
    pub(crate) fn commit<L: ProverParticipants<States = S>>(
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        witnesses: &L::Witnesses,
        rng: &mut impl PrivateRandom,
    ) -> Result<(Self, PolygeroCommitment), PolygeroError> {
        let param = t.part();
        param.participants.validate_witnesses(witnesses)?;
        let states = param.participants.encode(witnesses, rng);
        let oracle = ColumnOracle::new(param.config.n, rng, |j, h| {
            param.participants.append_encoded(&states, j, h)
        });
        let com = PolygeroCommitment {
            root: oracle.root(),
        };
        param.receive(&com, &mut t.transcript());
        Ok((
            Self {
                session: t.session(),
                states,
                oracle,
            },
            com,
        ))
    }
    /// Open the commitment on the session that received it, for
    /// `statements`, the equations of every field. It draws the batching
    /// weights at the current boundary, which must follow the last message
    /// any statement depends on, and consumes them (transcript I8).
    pub(crate) fn prove<L: ProverParticipants<States = S>>(
        self,
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        statements: L::Statements,
    ) -> Result<JointPolygeroProof<L::Bodies>, PolygeroError> {
        ensure(self.session == t.session(), "joint prover session mismatch")?;
        let p = t.part();
        // The rows must have been encoded for this parameter's geometry.
        p.participants.validate_states(&self.states)?;
        p.participants.validate_statements(&statements)?;
        let weights = p.weights_for(&statements, &mut t.transcript());
        let mut bodies = p.participants.respond(&self.states, &statements, &weights);
        // The statements and challenge polynomials are no longer needed
        // while collecting openings.
        drop((statements, weights));
        let indices = p.queries(&bodies, &mut t.transcript());
        p.participants.gather(&self.states, &mut bodies, &indices);
        Ok(JointPolygeroProof {
            bodies,
            opening: self.oracle.open(&indices),
        })
    }
}
/// The bare joint opening for tests and benchmarks outside the crate, on a
/// session bound with `Transcript::bound_for_test`.
#[cfg(feature = "testonly")]
impl<S> JointPolygeroProver<S> {
    /// `commit` on a bare session.
    pub fn commit_for_test<L: ProverParticipants<States = S>>(
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        witnesses: &L::Witnesses,
        rng: &mut impl PrivateRandom,
    ) -> Result<(Self, PolygeroCommitment), PolygeroError> {
        Self::commit(t, witnesses, rng)
    }
    /// `prove` on a bare session.
    pub fn prove_for_test<L: ProverParticipants<States = S>>(
        self,
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        statements: L::Statements,
    ) -> Result<JointPolygeroProof<L::Bodies>, PolygeroError> {
        self.prove(t, statements)
    }
}
/// Form the masked arithmetic response directly on the first 2k oracle
/// points. C_i is specified by its k logical samples; interpolate each row
/// with one plan and accumulate C_i*W_i using dense BLAS, then add V*u and z_R*m.
fn arithmetic_response<F: RuntimeField, D: EvaluationDomain<F>>(
    param: &PolygeroParam,
    w: &[Vec<F::E>],
    rows: &[Vec<F::E>],
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    let g = param.geom;
    let size = 2 * g.k;
    let encoder = domain.make_range(0..g.k, param.oracle_prefix(size));
    let mut response = vec![f.zero(); size];
    for row in 0..rows.len() {
        let extended = encoder.apply(&rows[row]);
        let w = &w[param.data_start() + row][..size];
        blas::vaxpy(&mut response, &extended, w, f);
    }
    let vanishing = super::polynomials::vanishing(&g, domain, f);
    blas::vaxpy(
        &mut response,
        &vanishing[..size],
        &w[param.u_row()][..size],
        f,
    );
    let selector = super::polynomials::selector(&g, domain, f);
    blas::vaxpy(
        &mut response,
        &selector[..size],
        &w[param.m_row()][..size],
        f,
    );
    response
}

/// Compute H = fstar + sum_{i=0}^{r-1} B_i*W_i, with W_r = fstar,
/// on its k+s response points.
/// Each B_i has degree at most s and is given by s+1 oracle-prefix samples.
/// One local interpolation plan serves every batched row.
fn primary_response<F: RuntimeField, D: EvaluationDomain<F>>(
    param: &PolygeroParam,
    w: &[Vec<F::E>],
    batching_samples: &[Vec<F::E>],
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    let g = param.geom;
    let dimension = g.k + g.s;
    let response = param.oracle_prefix(dimension);
    let mut h = w[param.fstar_row()][..dimension].to_vec();
    // Extend every B_i only to the oracle interval carrying the H response.
    let batching_encoder = domain.make_range(param.oracle_prefix(g.s + 1), response);
    for row in param.batched_rows() {
        let batching_values = batching_encoder.apply(&batching_samples[row]);
        blas::vaxpy(&mut h, &batching_values, &w[row][..dimension], f);
    }
    h
}

/// Form one field's responses before recursing to the next participant.
/// The dense constraint matrix is released before the next field is processed.
pub(super) fn respond<F: RuntimeField, D: EvaluationDomain<F>>(
    param: &PolygeroParam,
    w: &[Vec<F::E>],
    statement: &LinearStatement<F::E>,
    challenge: &FieldChallenges<F::E>,
    domain: &D,
    f: &F,
) -> FieldProof<F::E> {
    let h = primary_response(param, w, &challenge.batching_samples, domain, f);
    let rows =
        constraints::batch_constraints(param, &statement.b, &statement.a, &challenge.alpha, f);
    let z = arithmetic_response(param, w, &rows, domain, f);
    // Release this field's dense constraint matrix before processing the tail.
    drop(rows);
    FieldProof {
        h,
        z,
        rows: Vec::with_capacity(param.geom.nrow() * param.geom.t),
    }
}

pub(super) fn gather<E: Clone>(state: &[Vec<E>], body: &mut FieldProof<E>, indices: &[usize]) {
    for row in state {
        body.rows.extend(blas::gather(indices, row));
    }
}
