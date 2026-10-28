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

//! Encode and commit the v1 tableau, then produce its three masked responses.
//!
//! Ordinary rows interpolate a prefix of `block` samples. Product responses need
//! `dblock=2*block-1` samples; committed oracle columns start at dblock. The first
//! three rows mask the low-degree, dot-product and quadratic checks. Witness
//! rows follow, then separate groups of x, y and z product-copy rows.
//!
//! `prove` combines rows using transcript challenges, writes all response samples,
//! and only then samples the columns to open. BLAS handles dense combinations;
//! interpolation plans and work buffers are local to each response or layout
//! helper. The random sampling and row order follow the legacy wire convention.
use sha2::digest::Update;

use crate::{
    core::algebra::ElementOf,
    runtime::{
        algebra::{
            blas, InterpolationPlan, RangeInterpolatorFactory, RuntimeField, SubfieldV1,
            SupportsSampling,
        },
        ligero::{
            common::{inner_product_vector, layout_aext_into},
            param::{
                LigeroCommitment, LigeroLinearConstraint, LigeroParam, LigeroQuadraticConstraint,
            },
            tableau::Tableau,
            transcript::TranscriptLigero,
        },
        merkle::{commit, open, MerkleCommitment},
        proto::LigeroProof,
        random::{RandomEngine, Transcript},
    },
};

/// Encoded witness rows and the Merkle state needed to open their columns.
pub struct LigeroProver<const W: usize, F: RuntimeField<W>> {
    param: LigeroParam,
    mc: MerkleCommitment,
    tableau: Tableau<ElementOf<F>>,
}

impl<
        const W: usize,
        F: RuntimeField<W> + crate::core::algebra::SerializableField + SupportsSampling,
    > LigeroProver<W, F>
{
    /// Encode the witness and product copies, commit their columns, and bind the root.
    /// The caller declares witness[0..subfield_boundary] to be in the subfield.
    /// Only complete witness rows inside that prefix use subfield masks; other
    /// rows use full-field randomness. Boundary zero admits any witness values.
    #[allow(clippy::too_many_arguments)]
    pub fn commit<
        IF: RangeInterpolatorFactory<W, F>,
        R: RandomEngine,
        SF: SubfieldV1<E = ElementOf<F>>,
    >(
        subfield_boundary: usize,
        witness: &[ElementOf<F>],
        param: LigeroParam,
        ts: &mut Transcript,
        quadratic_constraints: &[LigeroQuadraticConstraint],
        make_interpolator: &IF,
        rng: &mut R,
        f: &F,
        sf: &SF,
    ) -> (Self, LigeroCommitment) {
        for val in &witness[..subfield_boundary] {
            debug_assert!(sf.contains(val), "element not in subfield");
        }

        let tableau = layout(
            subfield_boundary,
            witness,
            &param,
            quadratic_constraints,
            make_interpolator,
            rng,
            f,
            sf,
        );

        let len = f.serialized_size_bytes();
        let mut update_leaf_hash = |j: usize, sha: &mut sha2::Sha256| {
            let col_idx = j + param.dblock;
            let mut buf = [0u8; 128];
            for r in 0..param.nrow {
                let val = &tableau[(r, col_idx)];
                f.to_bytes_into(val, &mut buf[..len]);
                sha.update(&buf[..len]);
            }
        };

        // Merkle commitment
        let (mc, root) = commit(param.block_enc - param.dblock, rng, &mut update_leaf_hash);
        let commitment = LigeroCommitment { root };

        // P -> V
        ts.write_commitment(&commitment);

        (Self { param, mc, tableau }, commitment)
    }

    /// Returns a reference to the `LigeroParam`.
    #[must_use]
    pub fn param(&self) -> &LigeroParam {
        &self.param
    }

    /// Bind the statement digest, form all responses, then open the sampled columns.
    #[allow(clippy::too_many_arguments)]
    pub fn prove<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        linear_evals: &[ElementOf<F>],
        ts: &mut Transcript,
        linear_constraints: &[LigeroLinearConstraint<W, F>],
        hash_of_ligero_statement: &crate::runtime::merkle::Digest,
        quadratic_constraints: &[LigeroQuadraticConstraint],
        make_interpolator: &IF,
        f: &F,
    ) -> LigeroProof<W, F> {
        // P -> V theorem statement
        ts.write_ligero_statement(hash_of_ligero_statement);

        // V -> P
        let y_ldt = self.low_degree_proof(&ts.gen_uldt(&self.param, f), f);

        // V -> P
        let y_dot = {
            let nl = linear_evals.len();
            let alphal = ts.gen_alphal(nl, f);
            let alphaq = ts.gen_alphaq(&self.param, f);
            let a = inner_product_vector(
                &self.param,
                linear_constraints,
                &alphal,
                quadratic_constraints,
                &alphaq,
                f,
            );
            self.dot_proof(&a, make_interpolator, f)
        };

        // V -> P
        let (y_quad_0, y_quad_2) = self.quadratic_proof(&ts.gen_uquad(&self.param, f), f);

        // P -> V
        ts.write_elt_field_slice(&y_ldt, f);
        ts.write_elt_field_slice(&y_dot, f);
        ts.write_elt_field_slice(&y_quad_0, f);
        ts.write_elt_field_slice(&y_quad_2, f);

        // V -> P
        let idx = ts.gen_idx(&self.param);

        let req = self.gather_opened_columns(&idx);

        let merkle = open(&self.mc, &idx);

        // P -> V (final message) - Omitted to match C++ behavior

        LigeroProof {
            y_ldt,
            y_dot,
            y_quad_0,
            y_quad_2,
            req,
            merkle,
        }
    }

    /// Return the logical samples of mask_ldt + sum_i u_ldt[i]*W_i.
    fn low_degree_proof(&self, u_ldt: &[ElementOf<F>], f: &F) -> Vec<ElementOf<F>> {
        let mut y = self.tableau.row(self.param.ildt)[..self.param.block].to_vec();
        // All witness and quadratic rows with coefficient u_ldt[]
        for (i, u) in u_ldt.iter().enumerate().take(self.param.nwqrow) {
            blas::axpy(
                &mut y,
                u,
                &self.tableau.row(i + self.param.iw)[..self.param.block],
                f,
            );
        }
        y
    }

    /// Form mask_dot + sum_i A_i*W_i on 0..dblock. Each A_i has zeros in
    /// mask slots and the batched constraint coefficients in witness slots.
    fn dot_proof<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        a: &[ElementOf<F>],
        make_interpolator: &IF,
        f: &F,
    ) -> Vec<ElementOf<F>> {
        let interp_a =
            make_interpolator.make_range(0..self.param.block, self.param.block..self.param.dblock);
        let mut y = self.tableau.row(self.param.idot)[..self.param.dblock].to_vec();
        let mut a_ext = vec![f.zero(); self.param.dblock];

        for i in 0..self.param.nwqrow {
            layout_aext_into(&self.param, i, a, &mut a_ext, f);
            extend_row::<W, F>(&mut a_ext, self.param.block, &interp_a);

            // Accumulate y += A \otimes W.
            blas::vaxpy(
                &mut y,
                &a_ext,
                &self.tableau.row(i + self.param.iw)[..self.param.dblock],
                f,
            );
        }
        y
    }

    /// Form mask_quad + sum_i u_quad[i]*(Z_i-X_i*Y_i). Its witness slots
    /// vanish; transmit the prefix and suffix around that implicit zero interval.
    fn quadratic_proof(
        &self,
        u_quad: &[ElementOf<F>],
        f: &F,
    ) -> (Vec<ElementOf<F>>, Vec<ElementOf<F>>) {
        let mut y = self.tableau.row(self.param.iquad)[..self.param.dblock].to_vec();

        let iqx = self.param.iq;
        let iqy = iqx + self.param.nqtriples;
        let iqz = self.param.iq + 2 * self.param.nqtriples;

        let mut tmp = vec![f.zero(); self.param.dblock];
        for (i, _u) in u_quad.iter().enumerate().take(self.param.nqtriples) {
            // y[i] += u_quad[i] * (z[i] - x[i] * y[i])

            blas::copy(&mut tmp, &self.tableau.row(iqz + i)[..self.param.dblock]);

            // tmp[i] -= x[i] * y[i]
            blas::vymax(
                &mut tmp,
                &self.tableau.row(iqx + i)[..self.param.dblock],
                &self.tableau.row(iqy + i)[..self.param.dblock],
                f,
            );

            // y[i] += u_quad[i] * tmp[i]
            blas::axpy(&mut y, &u_quad[i], &tmp, f);
        }

        // Sanity check: the W part of Y is zero
        let ok = blas::equal0(&y[self.param.r..self.param.r + self.param.w], f);
        assert!(ok, "W part is nonzero");

        // Extract the first and last parts
        let y0 = y[..self.param.r].to_vec();
        let y2 = y[self.param.block..].to_vec();
        (y0, y2)
    }

    /// Gather each tableau row at the requested oracle columns. The legacy proof
    /// stores row-major opened values, with query order retained within each row.
    fn gather_opened_columns(&self, idx: &[usize]) -> Vec<ElementOf<F>> {
        let mut req = Vec::with_capacity(self.param.nrow * self.param.nreq);
        for i in 0..self.param.nrow {
            let row_req = blas::gather(idx, &self.tableau.row(i)[self.param.dblock..]);
            req.extend(row_req);
        }
        req
    }
}

// Fill tableau[i, [0,n)] with random elements.
fn random_row<const W: usize, F: RuntimeField<W> + SupportsSampling, R: RandomEngine>(
    i: usize,
    n: usize,
    tableau: &mut Tableau<ElementOf<F>>,
    rng: &mut R,
    f: &F,
) {
    for j in 0..n {
        tableau[(i, j)] = rng.elt_field(f);
    }
}

/// Fill a declared subfield prefix in the existing tableau allocation.
fn random_subfield_row<SF: SubfieldV1, R: RandomEngine>(
    i: usize,
    n: usize,
    tableau: &mut Tableau<SF::E>,
    rng: &mut R,
    sf: &SF,
) {
    for j in 0..n {
        tableau[(i, j)] = rng.elt_subfield(sf);
    }
}

/// Preserve the systematic samples and write only their missing suffix.
fn extend_row<const W: usize, F: RuntimeField<W>>(
    row: &mut [F::E],
    samples: usize,
    encoder: &impl InterpolationPlan<W, F>,
) {
    let (source, destination) = row.split_at_mut(samples);
    destination.clone_from_slice(&encoder.apply(source));
}

/// Sample the three dedicated masks in legacy order. The dot mask has zero
/// witness-slot sum; the quadratic mask is zero at every witness slot.
fn layout_blinding_rows<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    IF: RangeInterpolatorFactory<W, F>,
    R: RandomEngine,
>(
    param: &LigeroParam,
    tableau: &mut Tableau<ElementOf<F>>,
    interp_block: &impl InterpolationPlan<W, F>,
    make_interpolator: &IF,
    rng: &mut R,
    f: &F,
) {
    // Low-degree blinding row
    random_row(param.ildt, param.block, tableau, rng, f);

    extend_row::<W, F>(tableau.row_mut(param.ildt), param.block, interp_block);

    // Blinds of size [DBLOCK]
    let interp_dblock =
        make_interpolator.make_range(0..param.dblock, param.dblock..param.block_enc);

    // Dot-product blinding row constrained to SUM(W) = 0. First
    // randomize the dblock:
    random_row(param.idot, param.dblock, tableau, rng, f);

    // Then constrain to sum(W) = 0
    let (idot, r, w) = (param.idot, param.r, param.w);
    let sum = blas::dot1(&tableau.row(idot)[r..r + w], f);
    f.sub(&mut tableau[(idot, r)], &sum);

    extend_row::<W, F>(tableau.row_mut(idot), param.dblock, &interp_dblock);

    // Quadratic-test blinding row constrained to W = 0. First randomize
    // the entire dblock:
    random_row(param.iquad, param.dblock, tableau, rng, f);

    // Then constrain to W = 0
    blas::clear(&mut tableau.row_mut(param.iquad)[r..r + w], f);

    extend_row::<W, F>(tableau.row_mut(param.iquad), param.dblock, &interp_dblock);
}

#[allow(clippy::too_many_arguments)]
/// Place each witness block after its random prefix, then extend that row.
fn layout_witness_rows<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    R: RandomEngine,
    SF: SubfieldV1<E = ElementOf<F>>,
>(
    subfield_boundary: usize,
    witness: &[ElementOf<F>],
    param: &LigeroParam,
    tableau: &mut Tableau<ElementOf<F>>,
    interp: &impl InterpolationPlan<W, F>,
    rng: &mut R,
    f: &F,
    sf: &SF,
) {
    let (r, w, iw, nw) = (param.r, param.w, param.iw, param.nw);
    // Witness row EXTEND([RANDOM[R], WITNESS[W]], BLOCK)
    for i in 0..param.nwrow {
        // TRUE if the entire row is in the subfield
        let subfield_only = (i + 1) * w <= subfield_boundary;

        let row_idx = i + iw;
        if subfield_only {
            random_subfield_row(row_idx, r, tableau, rng, sf);
        } else {
            random_row(row_idx, r, tableau, rng, f);
        }

        let max_col = std::cmp::min(w, nw - i * w);
        let row_slice = &mut tableau.row_mut(row_idx)[r..r + w];
        blas::copy(&mut row_slice[..max_col], &witness[i * w..i * w + max_col]);
        if max_col < w {
            blas::clear(&mut row_slice[max_col..w], f);
        }
        extend_row::<W, F>(tableau.row_mut(row_idx), param.block, interp);
    }
}

/// Copy product operands/results into separate x/y/z row groups. Their random
/// prefixes are sampled independently; equality to the originals is batched later.
fn layout_quadratic_rows<const W: usize, F: RuntimeField<W> + SupportsSampling, R: RandomEngine>(
    witness: &[ElementOf<F>],
    param: &LigeroParam,
    tableau: &mut Tableau<ElementOf<F>>,
    quadratic_constraints: &[LigeroQuadraticConstraint],
    interp: &impl InterpolationPlan<W, F>,
    rng: &mut R,
    f: &F,
) {
    let iqx = param.iq;
    let iqy = iqx + param.nqtriples;
    let iqz = param.iq + 2 * param.nqtriples;
    let (r, w, nq) = (param.r, param.w, param.nq);

    for i in 0..param.nqtriples {
        random_row(iqx + i, r, tableau, rng, f);
        random_row(iqy + i, r, tableau, rng, f);
        random_row(iqz + i, r, tableau, rng, f);

        let max_j = std::cmp::min(w, nq.saturating_sub(i * w));

        for j in 0..max_j {
            let l = &quadratic_constraints[j + i * w];
            debug_assert_eq!(
                witness[l.z],
                f.mulf(&witness[l.x], &witness[l.y]),
                "invalid quadratic constraints"
            );
            tableau[(iqx + i, j + r)] = witness[l.x].clone();
            tableau[(iqy + i, j + r)] = witness[l.y].clone();
            tableau[(iqz + i, j + r)] = witness[l.z].clone();
        }

        if max_j < w {
            blas::clear(&mut tableau.row_mut(iqx + i)[r + max_j..r + w], f);
            blas::clear(&mut tableau.row_mut(iqy + i)[r + max_j..r + w], f);
            blas::clear(&mut tableau.row_mut(iqz + i)[r + max_j..r + w], f);
        }
        extend_row::<W, F>(tableau.row_mut(iqx + i), param.block, interp);
        extend_row::<W, F>(tableau.row_mut(iqy + i), param.block, interp);
        extend_row::<W, F>(tableau.row_mut(iqz + i), param.block, interp);
    }
}

#[allow(clippy::too_many_arguments)]
/// Construct all rows in their committed order using one ordinary-row encoder.
fn layout<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    IF: RangeInterpolatorFactory<W, F>,
    R: RandomEngine,
    SF: SubfieldV1<E = ElementOf<F>>,
>(
    subfield_boundary: usize,
    witness: &[ElementOf<F>],
    param: &LigeroParam,
    quadratic_constraints: &[LigeroQuadraticConstraint],
    make_interpolator: &IF,
    rng: &mut R,
    f: &F,
    sf: &SF,
) -> Tableau<ElementOf<F>> {
    let mut tableau = Tableau::new(param.nrow, param.block_enc, f.zero());
    let encoder = make_interpolator.make_range(0..param.block, param.block..param.block_enc);
    layout_blinding_rows(param, &mut tableau, &encoder, make_interpolator, rng, f);
    layout_witness_rows(
        subfield_boundary,
        witness,
        param,
        &mut tableau,
        &encoder,
        rng,
        f,
        sf,
    );
    layout_quadratic_rows(
        witness,
        param,
        &mut tableau,
        quadratic_constraints,
        &encoder,
        rng,
        f,
    );
    tableau
}
