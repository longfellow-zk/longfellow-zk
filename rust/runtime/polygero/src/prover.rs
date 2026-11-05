// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Commitment and responses for a typed list of fields.
use super::{
    ensure, joint::*, prover_commitment::ColumnOracle, PolygeroCommitment, PolygeroError,
    PolygeroParam,
};
use crate::runtime::{
    algebra::{blas, EvaluationDomain, InterpolationPlan, RuntimeField},
    proto::Digest,
    random::{RandomEngine, Transcript},
};
pub struct JointPolygeroProver<S> {
    pub(super) context: Digest,
    pub(super) states: S,
    pub(super) oracle: ColumnOracle,
}
impl<S> JointPolygeroProver<S> {
    pub fn commit<L: Participants<States = S>>(
        param: &JointPolygeroParam<L>,
        witnesses: L::Witnesses,
        t: &mut Transcript,
        rng: &mut impl RandomEngine,
    ) -> Result<(Self, PolygeroCommitment), PolygeroError> {
        param.participants.validate_witnesses(&witnesses)?;
        let states = param.participants.encode(witnesses, rng);
        let oracle = ColumnOracle::new(param.config.n, &param.context, rng, |j, h| {
            param.participants.append_encoded(&states, j, h)
        });
        let com = PolygeroCommitment {
            root: oracle.root(),
        };
        param.receive(&com, t);
        Ok((
            Self {
                context: param.context,
                states,
                oracle,
            },
            com,
        ))
    }
    pub fn prove<L: Participants<States = S>>(
        self,
        param: &JointPolygeroParam<L>,
        s: &L::Statements,
        t: &mut Transcript,
    ) -> Result<JointPolygeroProof<L::Bodies>, PolygeroError> {
        let p = param;
        ensure(self.context == p.context, "joint prover parameter mismatch")?;
        p.participants.validate_statements(s)?;
        let c = p.challenges(s, t);
        let mut bodies = p.participants.respond(&self.states, s, &c);
        // Challenge polynomials are no longer needed while collecting openings.
        drop(c);
        let indices = p.queries(&bodies, t);
        p.participants.gather(&self.states, &mut bodies, &indices);
        Ok(JointPolygeroProof {
            context: p.context,
            bodies,
            opening: self.oracle.open(&indices),
        })
    }
}
/// Form the masked arithmetic response directly on the first 2k oracle
/// points. C_i is specified by its k logical samples; interpolate each row
/// with one plan and accumulate C_i*W_i using dense BLAS, then add V*u and z_R*m.
pub(super) fn arithmetic_response<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
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
pub(super) fn primary_response<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
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
