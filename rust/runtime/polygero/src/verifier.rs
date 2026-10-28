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

//! Verify the masked responses against authenticated columns of W.
//!
//! Receive the commitment before the caller runs sumcheck. Once A and b are
//! known, replay the batching challenges and column queries, authenticate those
//! columns, and check the two response identities:
//!
//! ```text
//! H = fstar + sum_{i=0}^{r-1} B_i*W_i,
//! Z = sum_{data rows i} C_i*W_i + V*u + z_R*m.
//! ```
//! W_r = fstar is the final row; every preceding row receives a B_i.
//! C_i contains the alpha-weighted linear and copy-constraint coefficients for
//! row i; B_i is its primary batching polynomial. The rows fstar, u and m mask
//! the two responses.
//!
//! Product-output rows are virtual. Reconstruct W_z = W_x*W_y at the queries
//! before authenticating columns; the commitment and both responses include
//! these reconstructed values in the same row order as the prover's full W.
//!
//! H and Z come as oracle-prefix samples, so their lengths enforce their
//! dimension bounds. For logical points d_j = domain.point(j), also check
//!
//! ```text
//! tau = sum_{c=0}^{b.len()-1} alpha[c]*b[c],
//! sum_{j=t}^{k-1} Z(d_j) + tau = 0.
//! ```
//!
//! This global sum connects the column checks to A*w + b = 0. Copy constraints
//! contribute zero constants, so tau contains only the original b terms.
//!
//! Public polynomials use the shared interpolation and constraint code. Gather
//! their queried values for dense BLAS checks against the proof's packed rows.
//! Received and reconstructed rows are contiguous and need no transposition.
use super::{
    constraints, ensure, hash, transcript, PolygeroCommitment, PolygeroError, PolygeroLinearTerm,
    PolygeroParam, PolygeroProof,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            blas, range_interpolation::interpolate_range, EvaluationDomain, InterpolationPlan,
            RuntimeField, SupportsSampling,
        },
        merkle::heap::verify_proof_with_hash,
        proto::Digest,
        random::Transcript,
    },
};

/// Prepared public parameters and the commitment received for this invocation.
/// The transcript is passed explicitly so other protocols can run between
/// commitment reception and Polygero verification.
pub struct PolygeroVerifier {
    param: PolygeroParam,
    commitment: Option<PolygeroCommitment>,
}
impl PolygeroVerifier {
    /// Prepare immutable parameters; the caller must receive a root before verification.
    pub fn new(param: PolygeroParam) -> Self {
        Self {
            param,
            commitment: None,
        }
    }

    /// Bind the root before drawing any challenges that depend on it.
    /// Longfellow v2 then runs sumcheck on the same transcript before verify().
    pub fn receive_commitment(&mut self, commitment: &PolygeroCommitment, ts: &mut Transcript) {
        transcript::receive_commitment(ts, &self.param, commitment);
        self.commitment = Some(commitment.clone());
    }

    /// Reconstruct packed rows, authenticate their columns, then check H
    /// followed by Z over every sampled oracle column.
    /// The caller derives `statement` from the source statement and compiles its
    /// A and b locally, using the same convention as the prover.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
        D: EvaluationDomain<W, F>,
    >(
        &self,
        b: &[F::E],
        commitment: &PolygeroCommitment,
        proof: &PolygeroProof<F::E>,
        a: &[PolygeroLinearTerm<F::E>],
        statement: &Digest,
        ts: &mut Transcript,
        domain: &D,
        f: &F,
    ) -> Result<(), PolygeroError> {
        self.validate::<W, F, D>(b, commitment, proof, a, domain)?;
        let challenge = transcript::challenges(ts, &self.param, b.len(), statement, f);
        let indices = transcript::queries(ts, &self.param, &proof.h, &proof.z, f);

        let opened = self.materialize_rows(&proof.rows, f);
        self.authenticate_columns(commitment, proof, &indices, &opened, f)?;
        self.verify_primary_response(
            proof,
            &indices,
            &challenge.batching_samples,
            &opened,
            domain,
            f,
        )?;

        let rows = constraints::batch_constraints(&self.param, b, a, &challenge.alpha, f);
        // Batch the constants of A*w + b = 0 as tau = sum_{c=0}^{b.len()-1} alpha[c]*b[c].
        // The arithmetic check keeps that sign: sum_{j=t}^{k-1} Z(d_j) + tau = 0.
        let tau = blas::dot(&challenge.alpha[..b.len()], b, f);
        self.verify_arithmetic(proof, &indices, &rows, &opened, &tau, domain, f)
    }

    /// Check commitment reception, domain identity, proof shape and constraint
    /// indices before reconstructing rows or advancing the transcript.
    fn validate<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
        &self,
        b: &[F::E],
        commitment: &PolygeroCommitment,
        proof: &PolygeroProof<F::E>,
        a: &[PolygeroLinearTerm<F::E>],
        domain: &D,
    ) -> Result<(), PolygeroError> {
        ensure(
            self.commitment.as_ref() == Some(commitment),
            "Polygero commitment was not received",
        )?;
        ensure(
            self.param.domain_id == domain.domain_id(),
            "interpolation domain mismatch",
        )?;
        proof.validate(&self.param.geom)?;
        constraints::validate(self.param.geom.nw, b.len(), a)
    }

    /// Restore the full W row order at the queries. Consume one proof row for
    /// each transmitted row; reconstruct each virtual z from the preceding x,y.
    fn materialize_rows<const W: usize, F: RuntimeField<W>>(
        &self,
        received: &[F::E],
        f: &F,
    ) -> Vec<F::E> {
        let g = self.param.geom;
        let mut rows = Vec::with_capacity(g.nrow() * g.t);
        let mut received = received.chunks_exact(g.t);
        for row in 0..g.nrow() {
            if self.param.is_product_output(row) {
                // Copy x into the new row and multiply by y in dense query order.
                let start = rows.len();
                rows.extend_from_within(start - 2 * g.t..start - g.t);
                let (inputs, z) = rows.split_at_mut(start);
                blas::mul(z, &inputs[start - g.t..], f);
            } else {
                rows.extend_from_slice(received.next().expect("validated proof row count"));
            }
        }
        rows
    }

    /// Hash each queried column from the full packed rows, including virtual z.
    /// Check the shared Merkle path against the root received into the transcript.
    fn authenticate_columns<F: SerializableField>(
        &self,
        commitment: &PolygeroCommitment,
        proof: &PolygeroProof<F::E>,
        indices: &[usize],
        opened: &[F::E],
        f: &F,
    ) -> Result<(), PolygeroError> {
        let g = self.param.geom;
        let mut leaves = Vec::with_capacity(indices.len());
        for query in 0..indices.len() {
            let j = indices[query];
            let column = opened.chunks_exact(g.t).map(|row| &row[query]);
            let salt = &proof.opening.nonce[query];
            leaves.push((j, hash::leaf(&self.param.context, j, column, salt, f)));
        }
        verify_proof_with_hash(
            g.n,
            &commitment.root,
            &proof.opening.path,
            &leaves,
            |left, right| hash::node(&self.param.context, left, right),
        )
        .map_err(|error| PolygeroError(error.to_string()))
    }

    /// Check H = fstar + sum_{i=0}^{r-1} B_i*W_i, with W_r = fstar,
    /// at all queried points. One local plan extends every B_i from its
    /// oracle-prefix samples.
    fn verify_primary_response<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
        &self,
        proof: &PolygeroProof<F::E>,
        indices: &[usize],
        batching_samples: &[Vec<F::E>],
        opened: &[F::E],
        domain: &D,
        f: &F,
    ) -> Result<(), PolygeroError> {
        let g = self.param.geom;
        let mut expected = self.row(opened, self.param.fstar_row()).to_vec();
        let encoder =
            domain.make_range(self.param.oracle_prefix(g.s + 1), self.param.oracle_range());
        for row in self.param.batched_rows() {
            let extended = encoder.apply(&batching_samples[row]);
            let coefficients = blas::gather(indices, &extended);
            let w = self.row(opened, row);
            blas::vaxpy(&mut expected, &coefficients, w, f);
        }
        let h = interpolate_range(g.k, &proof.h, self.param.oracle_range(), domain);
        ensure(
            blas::gather(indices, &h) == expected,
            "Polygero primary response check failed",
        )
    }

    /// Check the logical sum of Z and the identity Z = sum_i C_i*W_i + V*u + z_R*m
    /// at each queried oracle point. On logical witness slots V=0 and z_R=1;
    /// sum_{j=t}^{k-1} m(d_j) = 0. Thus the constraints A*w+b=0 require
    /// sum_{j=t}^{k-1} Z(d_j) + tau = 0, with tau = sum_c alpha[c]*b[c].
    #[allow(clippy::too_many_arguments)]
    fn verify_arithmetic<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
        &self,
        proof: &PolygeroProof<F::E>,
        indices: &[usize],
        rows: &[Vec<F::E>],
        opened: &[F::E],
        tau: &F::E,
        domain: &D,
        f: &F,
    ) -> Result<(), PolygeroError> {
        let g = self.param.geom;
        let z = interpolate_range(g.k, &proof.z, 0..g.k + g.n, domain);
        let sum = f.addf(&blas::dot1(&z[g.t..g.k], f), tau);
        ensure(f.is_zero(&sum), "Polygero global arithmetic sum failed")?;
        let actual = blas::gather(indices, &z[g.k..]);
        let mut expected = self.constraint_sum(rows, indices, opened, domain, f);
        let vanishing = blas::gather(indices, &super::polynomials::vanishing(&g, domain, f));
        let u = self.row(opened, self.param.u_row());
        blas::vaxpy(&mut expected, &vanishing, u, f);
        let selector = blas::gather(indices, &super::polynomials::selector(&g, domain, f));
        let m = self.row(opened, self.param.m_row());
        blas::vaxpy(&mut expected, &selector, m, f);
        ensure(actual == expected, "Polygero arithmetic check failed")
    }

    /// Evaluate each C_i from its logical samples and accumulate sum_i C_i*W_i
    /// over the queried columns. One local plan serves all data rows; gather C_i
    /// at the queries and use the contiguous W_i slice directly in dense BLAS.
    fn constraint_sum<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
        &self,
        rows: &[Vec<F::E>],
        indices: &[usize],
        opened: &[F::E],
        domain: &D,
        f: &F,
    ) -> Vec<F::E> {
        let g = self.param.geom;
        let encoder = domain.make_range(0..g.k, self.param.oracle_range());
        let mut sum = vec![f.zero(); indices.len()];
        for row in 0..rows.len() {
            let extended = encoder.apply(&rows[row]);
            let row_values = blas::gather(indices, &extended);
            let w = self.row(opened, self.param.data_start() + row);
            blas::vaxpy(&mut sum, &row_values, w, f);
        }
        sum
    }

    /// Borrow the t queried values of W[row] in transcript query order.
    fn row<'a, E>(&self, rows: &'a [E], row: usize) -> &'a [E] {
        let t = self.param.geom.t;
        &rows[row * t..(row + 1) * t]
    }
}
