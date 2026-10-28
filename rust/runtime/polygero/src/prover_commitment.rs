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

//! Build the masked polynomial rows W and commit their oracle columns.
//!
//! Rows are stored as u, m, ordinary witness rows, product triples, then fstar.
//! An ordinary row has k logical samples: t fresh masks followed by witness
//! values. Product inputs have dimension ceil(k/2), with the same mask prefix;
//! multiplying their encodings produces the third row with dimension at most k.
//!
//! Each row is evaluated on oracle points k..k+n. Every random masking
//! sample is uniform in the ambient field, independently of witness values.
//!
//! The final helper salts and hashes columns, then constructs their Merkle tree.
//! Interpolation plans are local to the encoding invocation that uses them.
use super::{ensure, hash, PolygeroError, PolygeroParam};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            blas, EvaluationDomain, InterpolationPlan, RuntimeField, SupportsSampling,
        },
        merkle::MerkleHeap,
        proto::MerkleNonce,
        random::RandomEngine,
    },
};

/// Validate witness shape and product identities before sampling.
pub(super) fn validate_witness<const W: usize, F: RuntimeField<W>>(param: &PolygeroParam, witness: &[F::E], f: &F) -> Result<(), PolygeroError> {
    ensure(witness.len() == param.geom.nw, "witness length mismatch")?;
    ensure(
        param
            .products
            .iter()
            .all(|p| f.mulf(&witness[p.x], &witness[p.y]) == witness[p.z]),
        "unsatisfied product constraint",
    )
}

/// Encode u and m, the ordinary rows and product triples, then fstar.
/// Own the witness so it is released before Merkle construction. Each helper
/// constructs the interpolation plans it uses.
pub(super) fn encode_rows<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    D: EvaluationDomain<W, F>,
    R: RandomEngine,
>(
    param: &PolygeroParam,
    witness: Vec<F::E>,
    domain: &D,
    rng: &mut R,
    f: &F,
) -> Vec<Vec<F::E>> {
    let g = param.geom;
    let mut w = Vec::with_capacity(g.nrow());
    encode_arithmetic_masks(&mut w, param, domain, rng, f);
    encode_ordinary_rows(&mut w, param, &witness, domain, rng, f);
    encode_product_rows(&mut w, param, &witness, domain, rng, f);
    encode_fstar(&mut w, param, domain, rng, f);
    w
}

/// Lay out each ordinary witness block after its T masking samples.
/// All rows use ambient-field masks, including rows with base-field witnesses.
fn encode_ordinary_rows<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    D: EvaluationDomain<W, F>,
    R: RandomEngine,
>(
    w: &mut Vec<Vec<F::E>>,
    param: &PolygeroParam,
    witness: &[F::E],
    domain: &D,
    rng: &mut R,
    f: &F,
) {
    let g = param.geom;
    let encoder = domain.make_range(0..g.k, param.oracle_range());
    let width = g.ordinary_width();
    for row in 0..g.ordinary_rows() {
        let end = ((row + 1) * width).min(witness.len());
        let values = &witness[row * width..end];
        let mut samples = rng.elt_field_slice(g.t, f);
        samples.resize(g.k, f.zero());
        blas::copy(&mut samples[g.t..g.t + values.len()], values);
        w.push(encoder.apply(&samples));
    }
}

/// Encode the two inputs of each product group with one local plan. Their
/// pointwise product is the third row, with degree below k by construction.
/// Both input rows always use full-field masks and interpolation.
/// All three rows enter the commitment; only the two input rows are transmitted.
fn encode_product_rows<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    D: EvaluationDomain<W, F>,
    R: RandomEngine,
>(
    w: &mut Vec<Vec<F::E>>,
    param: &PolygeroParam,
    witness: &[F::E],
    domain: &D,
    rng: &mut R,
    f: &F,
) {
    if param.products.is_empty() {
        return;
    }
    let g = param.geom;
    let dimension = g.product_dimension();
    let encoder = domain.make_range(0..dimension, param.oracle_range());
    for products in param.products.chunks(g.product_width()) {
        let mut samples_x = rng.elt_field_slice(g.t, f);
        samples_x.resize(dimension, f.zero());
        for j in 0..products.len() {
            samples_x[g.t + j] = witness[products[j].x].clone();
        }
        let x = encoder.apply(&samples_x);

        let mut samples_y = rng.elt_field_slice(g.t, f);
        samples_y.resize(dimension, f.zero());
        for j in 0..products.len() {
            samples_y[g.t + j] = witness[products[j].y].clone();
        }
        let y = encoder.apply(&samples_y);

        let mut z = x.clone();
        blas::mul(&mut z, &y, f);
        w.push(x);
        w.push(y);
        w.push(z);
    }
}

/// Encode the full-field primary mask fstar, of dimension K+S. Uniform
/// samples at any K+S distinct points specify a uniform polynomial of this dimension.
fn encode_fstar<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    D: EvaluationDomain<W, F>,
    R: RandomEngine,
>(
    w: &mut Vec<Vec<F::E>>,
    param: &PolygeroParam,
    domain: &D,
    rng: &mut R,
    f: &F,
) {
    let g = param.geom;
    let primary = rng.elt_field_slice(g.k + g.s, f);
    // Any distinct k+s samples give a uniform mask of degree below k+s.
    let encoder = domain.make_range(param.oracle_prefix(g.k + g.s), param.oracle_range());
    w.push(encoder.apply(&primary));
}

/// Encode the full-field arithmetic masks u and m. The free mask u starts at
/// the oracle prefix. Mask m is specified on the logical points, with its sum
/// over witness slots constrained to zero so z_R*m preserves the global sum.
fn encode_arithmetic_masks<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling,
    D: EvaluationDomain<W, F>,
    R: RandomEngine,
>(
    w: &mut Vec<Vec<F::E>>,
    param: &PolygeroParam,
    domain: &D,
    rng: &mut R,
    f: &F,
) {
    let g = param.geom;
    let u = rng.elt_field_slice(g.k, f);
    let encoder_u = domain.make_range(param.oracle_prefix(g.k), param.oracle_range());
    w.push(encoder_u.apply(&u));

    let mut m = rng.elt_field_slice(g.k, f);
    // Set m[t] = -sum_{j=t+1}^{k-1} m[j], so sum_{j=t}^{k-1} m[j] = 0.
    // The selector is zero on 0..t; those mask samples do not enter this sum.
    m[g.t] = f.neg(&blas::dot1(&m[g.t + 1..], f));
    let encoder_m = domain.make_range(0..g.k, param.oracle_range());
    w.push(encoder_m.apply(&m));
}

/// Salt and hash every encoded column, then build the canonical Merkle tree.
pub(super) fn commit_columns<F: SerializableField, R: RandomEngine>(
    param: &PolygeroParam,
    w: &[Vec<F::E>],
    rng: &mut R,
    f: &F,
) -> (MerkleHeap, Vec<MerkleNonce>) {
    let salts: Vec<_> = (0..param.geom.n)
        .map(|_| MerkleNonce {
            bytes: rng.bytes(32).try_into().unwrap(),
        })
        .collect();
    let leaves: Vec<_> = (0..param.geom.n)
        .map(|j| hash::leaf(&param.context, j, w.iter().map(|row| &row[j]), &salts[j], f))
        .collect();
    let tree = MerkleHeap::new_with_hash(&leaves, |l, r| hash::node(&param.context, l, r));
    (tree, salts)
}
