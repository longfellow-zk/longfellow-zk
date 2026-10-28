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

//! Commit the encoded witness W, then answer the public linear constraints.
//!
//! `commit` builds the masked rows and binds their Merkle root. The caller may
//! then run sumcheck on the same transcript to obtain A and b. `prove` binds
//! the caller's source-statement digest, samples batching challenges, and sends
//! two polynomials:
//!
//! ```text
//! H(x) = fstar(x) + sum_{i=0}^{r-1} B_i(x) W_i(x),
//! Z(x) = sum_{data rows i} C_i(x) W_i(x) + V(x) u(x) + z_R(x) m(x).
//! ```
//!
//! W_r = fstar is the final row; every preceding row receives a B_i.
//!
//! H is represented by k+s samples and Z by 2k samples, both starting at the
//! oracle's first point. Only after these responses are fixed do we sample
//! columns and construct their opening. The proof packs their values row by row,
//! retaining query order within each row, alongside both responses and the Merkle path.
//!
//! Interpolation plans and scratch buffers stay local to their consuming helpers.
//! Challenge storage and constraint rows end before gathering the opened columns.
use super::{
    constraints, ensure, prover_commitment, transcript, PolygeroCommitment, PolygeroError,
    PolygeroLinearTerm, PolygeroParam, PolygeroProof,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            blas, EvaluationDomain, InterpolationPlan, RuntimeField, SupportsSampling,
        },
        merkle::MerkleHeap,
        proto::{Digest, MerkleNonce, MerkleProof},
        random::{RandomEngine, Transcript},
    },
};

/// A commitment, its private rows, and the masks needed for responses.
pub struct PolygeroProver<const W: usize, F: RuntimeField<W>> {
    param: PolygeroParam,
    /// W in the paper: encoded polynomial rows, including masks, on oracle columns.
    w: Vec<Vec<F::E>>,
    tree: MerkleHeap,
    salts: Vec<MerkleNonce>,
}
impl<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>
    PolygeroProver<W, F>
{
    /// Validate and encode the witness, commit its columns, and bind the root.
    /// Every witness and mask cell is an ambient-field element.
    #[allow(clippy::too_many_arguments)]
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine>(
        witness: Vec<F::E>,
        param: PolygeroParam,
        ts: &mut Transcript,
        domain: &D,
        rng: &mut R,
        f: &F,
    ) -> Result<(Self, PolygeroCommitment), PolygeroError> {
        ensure(
            param.domain_id == domain.domain_id(),
            "interpolation domain mismatch",
        )?;
        prover_commitment::validate_witness(&param, &witness, f)?;
        let w =
            prover_commitment::encode_rows(&param, witness, domain, rng, f);
        let (tree, salts) = prover_commitment::commit_columns(&param, &w, rng, f);
        let commitment = PolygeroCommitment { root: tree.root() };
        transcript::receive_commitment(ts, &param, &commitment);
        Ok((
            Self {
                param,
                w,
                tree,
                salts,
            },
            commitment,
        ))
    }

    /// Prove A*w + b = 0 and the product constraints fixed at commitment.
    /// Consumes the prover state.
    /// `statement` identifies the source statement implemented by A and b;
    /// it may depend on a protocol run after commitment, such as sumcheck.
    /// Validate constraint indices before sampling the response challenges.
    pub fn prove<D: EvaluationDomain<W, F>>(
        self,
        b: &[F::E],
        ts: &mut Transcript,
        a: &[PolygeroLinearTerm<F::E>],
        statement: &Digest,
        domain: &D,
        f: &F,
    ) -> Result<PolygeroProof<F::E>, PolygeroError> {
        ensure(
            self.param.domain_id == domain.domain_id(),
            "interpolation domain mismatch",
        )?;
        constraints::validate(self.param.geom.nw, b.len(), a)?;
        let (h, z) = self.responses(b, a, statement, ts, domain, f);
        let (rows, opening) = {
            let indices = transcript::queries(ts, &self.param, &h, &z, f);
            self.open_columns(&indices)
        };
        Ok(PolygeroProof {
            h,
            z,
            rows,
            opening,
        })
    }

    /// Sample the shared challenges, then form H and Z in that order.
    fn responses<D: EvaluationDomain<W, F>>(
        &self,
        b: &[F::E],
        a: &[PolygeroLinearTerm<F::E>],
        statement: &Digest,
        ts: &mut Transcript,
        domain: &D,
        f: &F,
    ) -> (Vec<F::E>, Vec<F::E>) {
        let challenge = transcript::challenges(ts, &self.param, b.len(), statement, f);
        let h = self.primary_response(&challenge.batching_samples, domain, f);
        let rows = constraints::batch_constraints(&self.param, b, a, &challenge.alpha, f);
        let z = self.arithmetic_response(&rows, domain, f);
        (h, z)
    }

    /// Form the masked arithmetic response directly on the first 2k oracle
    /// points. C_i is specified by its k logical samples; interpolate each row
    /// with one plan and accumulate C_i*W_i using dense BLAS, then add V*u and z_R*m.
    fn arithmetic_response<D: EvaluationDomain<W, F>>(
        &self,
        rows: &[Vec<F::E>],
        domain: &D,
        f: &F,
    ) -> Vec<F::E> {
        let g = self.param.geom;
        let size = 2 * g.k;
        let encoder = domain.make_range(0..g.k, self.param.oracle_prefix(size));
        let mut response = vec![f.zero(); size];
        for row in 0..rows.len() {
            let extended = encoder.apply(&rows[row]);
            let w = &self.w[self.param.data_start() + row][..size];
            blas::vaxpy(&mut response, &extended, w, f);
        }
        let vanishing = super::polynomials::vanishing(&g, domain, f);
        blas::vaxpy(
            &mut response,
            &vanishing[..size],
            &self.w[self.param.u_row()][..size],
            f,
        );
        let selector = super::polynomials::selector(&g, domain, f);
        blas::vaxpy(
            &mut response,
            &selector[..size],
            &self.w[self.param.m_row()][..size],
            f,
        );
        response
    }

    /// Compute H = fstar + sum_{i=0}^{r-1} B_i*W_i, with W_r = fstar,
    /// on its k+s response points.
    /// Each B_i has degree at most s and is given by s+1 oracle-prefix samples.
    /// One local interpolation plan serves every batched row.
    fn primary_response<D: EvaluationDomain<W, F>>(
        &self,
        batching_samples: &[Vec<F::E>],
        domain: &D,
        f: &F,
    ) -> Vec<F::E> {
        let g = self.param.geom;
        let dimension = g.k + g.s;
        let response = self.param.oracle_prefix(dimension);
        let mut h = self.w[self.param.fstar_row()][..dimension].to_vec();
        // Extend every B_i only to the oracle interval carrying the H response.
        let batching_encoder = domain.make_range(self.param.oracle_prefix(g.s + 1), response);
        for row in self.param.batched_rows() {
            let batching_values = batching_encoder.apply(&batching_samples[row]);
            blas::vaxpy(&mut h, &batching_values, &self.w[row][..dimension], f);
        }
        h
    }

    /// Gather the selected columns of each W row, retaining transcript query order.
    /// Omit product-output rows: the verifier reconstructs z = x*y from each pair.
    /// The remaining rows are consecutive, with indices.len() values per row.
    fn open_columns(&self, indices: &[usize]) -> (Vec<F::E>, MerkleProof) {
        let g = self.param.geom;
        let mut rows = Vec::with_capacity(indices.len() * g.transmitted_rows());
        for row in 0..self.w.len() {
            if !self.param.is_product_output(row) {
                rows.extend(blas::gather(indices, &self.w[row]));
            }
        }
        let opening = MerkleProof {
            nonce: blas::gather(indices, &self.salts),
            path: self.tree.generate_proof(indices),
        };
        (rows, opening)
    }
}

#[cfg(test)]
#[path = "../tests/reference.rs"]
pub(super) mod reference;
