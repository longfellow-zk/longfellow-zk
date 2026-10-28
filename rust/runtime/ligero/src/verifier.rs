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

//! Verify the v1 Ligero responses against authenticated oracle columns.
//!
//! Validate proof lengths and sparse constraint indices before transcript replay.
//! Reproduce the batching weights, absorb all response samples, and choose the
//! opened columns. Merkle authentication then precedes three algebraic checks:
//! the low-degree row combination, the batched dot-product polynomial and its
//! logical sum, and the weighted product residuals Z_i-X_i*Y_i.
//!
//! Ordinary rows interpolate from 0..block; product responses use 0..dblock.
//! Both are evaluated on the oracle dblock..block_enc and gathered at the sampled
//! indices. Openings are already row-major, so their combinations use dense BLAS.
use sha2::digest::Update;

use crate::{
    core::algebra::ElementOf,
    runtime::{
        algebra::{
            blas, InterpolationPlan, RangeInterpolatorFactory, RuntimeField, SupportsSampling,
        },
        ligero::{
            common::{inner_product_vector, layout_aext_into},
            param::{
                LigeroCommitment, LigeroLinearConstraint, LigeroParam, LigeroQuadraticConstraint,
            },
            transcript::TranscriptLigero,
            LigeroError,
        },
        proto::LigeroProof,
        random::Transcript,
    },
};

/// Borrow the current transcript and the immutable legacy layout for verification.
pub struct LigeroVerifier<'a> {
    ts: &'a mut Transcript,
    param: &'a LigeroParam,
}

impl<'a> LigeroVerifier<'a> {
    pub fn new(ts: &'a mut Transcript, param: &'a LigeroParam) -> Self {
        Self { ts, param }
    }

    /// Replays commitment transmission from P to V.
    pub fn receive_commitment(&mut self, commitment: &LigeroCommitment) {
        // P -> V
        self.ts.write_commitment(commitment);
    }

    /// Main verification algorithm for Ligero arguments.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<
        const W: usize,
        F: RuntimeField<W> + crate::core::algebra::SerializableField + SupportsSampling,
        IF: RangeInterpolatorFactory<W, F>,
    >(
        &mut self,
        linear_evals: &[ElementOf<F>],
        commitment: &LigeroCommitment,
        proof: &LigeroProof<W, F>,
        linear_constraints: &[LigeroLinearConstraint<W, F>],
        hash_of_ligero_statement: &crate::runtime::merkle::Digest,
        quadratic_constraints: &[LigeroQuadraticConstraint],
        make_interpolator: &IF,
        f: &F,
    ) -> Result<(), LigeroError> {
        self.validate(
            proof,
            linear_evals.len(),
            linear_constraints,
            quadratic_constraints,
        )?;

        // Batching weights follow the committed tableau. Column queries follow
        // all responses, linking the claimed combinations to that same tableau.

        // P -> V theorem statement
        self.ts.write_ligero_statement(hash_of_ligero_statement);

        // V -> P
        let u_ldt = self.ts.gen_uldt(self.param, f);

        // V -> P
        let alphal = self.ts.gen_alphal(linear_evals.len(), f);
        let alphaq = self.ts.gen_alphaq(self.param, f);

        // V -> P
        let u_quad = self.ts.gen_uquad(self.param, f);

        // P -> V
        self.ts.write_elt_field_slice(&proof.y_ldt, f);
        self.ts.write_elt_field_slice(&proof.y_dot, f);
        self.ts.write_elt_field_slice(&proof.y_quad_0, f);
        self.ts.write_elt_field_slice(&proof.y_quad_2, f);

        // V -> P
        let idx = self.ts.gen_idx(self.param);

        // P -> V (final message) - Omitted to match C++ behavior

        self.merkle_check(&idx, commitment, proof, f)
            .map_err(LigeroError::MerkleCheckFailed)?;

        let response_encoder = {
            let ordinary_encoder = make_interpolator
                .make_range(0..self.param.block, self.param.dblock..self.param.block_enc);
            if !self.low_degree_check(&idx, &u_ldt, proof, &ordinary_encoder, f) {
                return Err(LigeroError::LowDegreeCheckFailed);
            }

            let a = inner_product_vector(
                self.param,
                linear_constraints,
                &alphal,
                quadratic_constraints,
                &alphaq,
                f,
            );
            let response_encoder = make_interpolator.make_range(
                0..self.param.dblock,
                self.param.dblock..self.param.block_enc,
            );
            if !self.dot_check(&idx, &a, proof, &ordinary_encoder, &response_encoder, f) {
                return Err(LigeroError::DotCheckFailed);
            }
            response_encoder
        };

        // Check the putative value of the inner product for linear constraint A w + b = 0.
        // proof_dot = alpha_L . (A w)
        // want_dot  = alpha_L . b
        // Requirement: proof_dot + want_dot == 0
        let want_dot = blas::dot(linear_evals, &alphal, f);
        let proof_dot = blas::dot1(&proof.y_dot[self.param.r..self.param.r + self.param.w], f);

        let mut sum = proof_dot;
        f.add(&mut sum, &want_dot);

        if sum != f.zero() {
            return Err(LigeroError::LinearInnerProductMismatch);
        }

        if !self.quadratic_check(&idx, &u_quad, proof, &response_encoder, f) {
            return Err(LigeroError::QuadraticCheckFailed);
        }

        Ok(())
    }

    /// Check the legacy shape and index conditions in their original error order.
    /// This precedes all transcript sampling and indexing into untrusted messages.
    fn validate<const W: usize, F: RuntimeField<W> + crate::core::algebra::SerializableField>(
        &self,
        proof: &LigeroProof<W, F>,
        nequations: usize,
        linear_constraints: &[LigeroLinearConstraint<W, F>],
        quadratic_constraints: &[LigeroQuadraticConstraint],
    ) -> Result<(), LigeroError> {
        if proof.y_ldt.len() != self.param.block {
            return Err(LigeroError::InvalidProof(
                "invalid y_ldt length".to_string(),
            ));
        }
        if proof.y_dot.len() != self.param.dblock {
            return Err(LigeroError::InvalidProof(
                "invalid y_dot length".to_string(),
            ));
        }
        if proof.y_quad_0.len() != self.param.r {
            return Err(LigeroError::InvalidProof(
                "invalid y_quad_0 length".to_string(),
            ));
        }
        if proof.y_quad_2.len() != self.param.dblock - self.param.block {
            return Err(LigeroError::InvalidProof(
                "invalid y_quad_2 length".to_string(),
            ));
        }
        if proof.req.len() != self.param.nrow * self.param.nreq {
            return Err(LigeroError::InvalidProof("invalid req length".to_string()));
        }
        for term in linear_constraints {
            if term.w >= self.param.nw || term.c >= nequations {
                return Err(LigeroError::InvalidProof(
                    "linear constraint index out of bounds".to_string(),
                ));
            }
        }
        if quadratic_constraints.len() < self.param.nq {
            return Err(LigeroError::InvalidProof(
                "invalid quadratic constraints length".to_string(),
            ));
        }
        for l in &quadratic_constraints[..self.param.nq] {
            if l.x >= self.param.nw || l.y >= self.param.nw || l.z >= self.param.nw {
                return Err(LigeroError::InvalidProof(
                    "quadratic constraint index out of bounds".to_string(),
                ));
            }
        }
        Ok(())
    }

    /// Extend a response onto the oracle and return only the requested columns.
    /// The full extension buffer ends here, before the caller combines values.
    fn interpolate_req_columns<const W: usize, F: RuntimeField<W>>(
        &self,
        idx: &[usize],
        y: &[F::E],
        encoder: &impl InterpolationPlan<W, F>,
    ) -> Vec<F::E> {
        let yext = encoder.apply(y);
        blas::gather(idx, &yext)
    }

    /// Hash opened values in committed column order and verify the shared path.
    fn merkle_check<
        const W: usize,
        F: RuntimeField<W> + crate::core::algebra::SerializableField,
    >(
        &self,
        idx: &[usize],
        commitment: &LigeroCommitment,
        proof: &LigeroProof<W, F>,
        f: &F,
    ) -> Result<(), crate::runtime::merkle::MerkleError> {
        let len = f.serialized_size_bytes();
        let mut updhash = |r: usize, _col_idx: usize, sha: &mut sha2::Sha256| {
            let mut buf = [0u8; 128];
            for i in 0..self.param.nrow {
                let val = &proof.req[i * self.param.nreq + r];
                f.to_bytes_into(val, &mut buf[..len]);
                sha.update(&buf[..len]);
            }
        };

        crate::runtime::merkle::verify(
            self.param.block_enc - self.param.dblock,
            &commitment.root,
            idx,
            &proof.merkle,
            &mut updhash,
        )
    }

    /// Compare the interpolated low-degree response with its opened row combination.
    fn low_degree_check<
        const W: usize,
        F: RuntimeField<W> + crate::core::algebra::SerializableField,
    >(
        &self,
        idx: &[usize],
        u_ldt: &[F::E],
        proof: &LigeroProof<W, F>,
        encoder: &impl InterpolationPlan<W, F>,
        f: &F,
    ) -> bool {
        // The ILDT blinding row with coefficient 1
        let mut yc = proof.req
            [self.param.ildt * self.param.nreq..(self.param.ildt + 1) * self.param.nreq]
            .to_vec();

        // All remaining witness and quadratic rows with coefficient u_ldt[]
        for (i, u_ldt_elt) in u_ldt.iter().enumerate().take(self.param.nwqrow) {
            blas::axpy(
                &mut yc,
                u_ldt_elt,
                &proof.req[(i + self.param.iw) * self.param.nreq
                    ..(i + self.param.iw + 1) * self.param.nreq],
                f,
            );
        }

        let yp = self.interpolate_req_columns(idx, &proof.y_ldt, encoder);

        blas::equal(&yp, &yc)
    }

    /// At every opened column, check y_dot = mask_dot + sum_i A_i*W_i.
    fn dot_check<const W: usize, F: RuntimeField<W> + crate::core::algebra::SerializableField>(
        &self,
        idx: &[usize],
        a: &[F::E],
        proof: &LigeroProof<W, F>,
        ordinary_encoder: &impl InterpolationPlan<W, F>,
        response_encoder: &impl InterpolationPlan<W, F>,
        f: &F,
    ) -> bool {
        // The IDOT blinding row with coefficient 1
        let mut yc = proof.req
            [self.param.idot * self.param.nreq..(self.param.idot + 1) * self.param.nreq]
            .to_vec();

        {
            let mut samples = vec![f.zero(); self.param.block];
            for i in 0..self.param.nwqrow {
                layout_aext_into(self.param, i, a, &mut samples, f);
                let a_ext = ordinary_encoder.apply(&samples);
                let a_req = blas::gather(idx, &a_ext);

                // Accumulate yc += A[i] \otimes W[i].
                blas::vaxpy(
                    &mut yc,
                    &a_req,
                    &proof.req[(i + self.param.iw) * self.param.nreq
                        ..(i + self.param.iw + 1) * self.param.nreq],
                    f,
                );
            }
        }

        let yp = self.interpolate_req_columns(idx, &proof.y_dot, response_encoder);
        blas::equal(&yp, &yc)
    }

    /// Reinsert the implicit zero witness interval, then check the weighted
    /// product residuals against the quadratic response at each opened column.
    fn quadratic_check<
        const W: usize,
        F: RuntimeField<W> + crate::core::algebra::SerializableField,
    >(
        &self,
        idx: &[usize],
        u_quad: &[F::E],
        proof: &LigeroProof<W, F>,
        encoder: &impl InterpolationPlan<W, F>,
        f: &F,
    ) -> bool {
        // The IQUAD blinding row with coefficient 1
        let mut yc = proof.req
            [self.param.iquad * self.param.nreq..(self.param.iquad + 1) * self.param.nreq]
            .to_vec();

        {
            let (iqx, iqy, iqz) = (
                self.param.iq,
                self.param.iq + self.param.nqtriples,
                self.param.iq + 2 * self.param.nqtriples,
            );

            let mut tmp = vec![f.zero(); self.param.nreq];
            // All quadratic triples with coefficient u_quad[]
            for (i, u_quad_elt) in u_quad.iter().enumerate().take(self.param.nqtriples) {
                // yc += u_quad[i] * (z[i] - x[i] * y[i])

                // tmp = z[i]
                blas::copy(
                    &mut tmp,
                    &proof.req[(iqz + i) * self.param.nreq..(iqz + i + 1) * self.param.nreq],
                );

                // tmp -= x[i] \otimes y[i]
                blas::vymax(
                    &mut tmp,
                    &proof.req[(iqx + i) * self.param.nreq..(iqx + i + 1) * self.param.nreq],
                    &proof.req[(iqy + i) * self.param.nreq..(iqy + i + 1) * self.param.nreq],
                    f,
                );

                // yc += u_quad[i] * tmp
                blas::axpy(&mut yc, u_quad_elt, &tmp, f);
            }
        }

        // Reconstruct y_quad from the two parts in the proof
        let mut yquad = proof.y_quad_0.clone();
        yquad.resize(self.param.block, f.zero());
        yquad.extend_from_slice(&proof.y_quad_2);

        // Interpolate y_quad at the opened columns
        let yp = self.interpolate_req_columns(idx, &yquad, encoder);

        blas::equal(&yp, &yc)
    }
}
