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

//! Build the masked polynomial rows W for the shared column oracle.
//!
//! Rows are stored as u, m, witness rows, then fstar.
//! A witness row has k logical samples: t fresh masks followed by witness values.
//!
//! Each row is evaluated on oracle points k..k+n. Every random masking
//! sample is uniform in the ambient field, independently of witness values.
//!
//! Interpolation plans are local to the encoding invocation that uses them.
use super::PolygeroParam;
use crate::runtime::{
    algebra::{blas, EvaluationDomain, InterpolationPlan, RuntimeField, SupportsSampling},
    random::RandomEngine,
};

/// Encode u and m, the witness rows, then fstar.
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
    encode_witness_rows(&mut w, param, &witness, domain, rng, f);
    encode_fstar(&mut w, param, domain, rng, f);
    w
}

/// Lay out each ordinary witness block after its T masking samples.
/// All rows use ambient-field masks, including rows with base-field witnesses.
fn encode_witness_rows<
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
    let width = g.row_width();
    for row in 0..g.data_rows() {
        let end = ((row + 1) * width).min(witness.len());
        let values = &witness[row * width..end];
        let mut samples = rng.elt_field_slice(g.t, f);
        samples.resize(g.k, f.zero());
        blas::copy(&mut samples[g.t..g.t + values.len()], values);
        w.push(encoder.apply(&samples));
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

use sha2::{Digest as _, Sha256};

use super::hash::leaf;
use crate::runtime::{
    v2::merkle::MerkleHeap,
    v2::proto::{Digest, MerkleNonce, MerkleProof, NONCE_LEN},
};
pub(super) struct ColumnOracle {
    pub(super) tree: MerkleHeap,
    pub(super) salts: Vec<MerkleNonce>,
}
impl ColumnOracle {
    /// `append` streams every participant's column into one leaf hash. Field
    /// arithmetic stays in the participant traversal; this tree only sees bytes.
    pub(super) fn new(
        n: usize,
        context: &Digest,
        rng: &mut impl RandomEngine,
        mut append: impl FnMut(usize, &mut Sha256),
    ) -> Self {
        let salts: Vec<_> = (0..n)
            .map(|_| MerkleNonce {
                bytes: rng.bytes(NONCE_LEN).try_into().unwrap(),
            })
            .collect();
        let leaves: Vec<_> = (0..n)
            .map(|j| {
                let mut h = leaf(context, j, &salts[j]);
                append(j, &mut h);
                Digest {
                    data: h.finalize().into(),
                }
            })
            .collect();
        Self {
            tree: MerkleHeap::new(context, &leaves),
            salts,
        }
    }
    pub(super) fn root(&self) -> Digest {
        self.tree.root()
    }
    pub(super) fn open(&self, indices: &[usize]) -> MerkleProof {
        // Nonces follow query order, just like the opened values in each field.
        // MerkleHeap separately defines the canonical authentication frontier.
        MerkleProof {
            nonce: indices.iter().map(|&j| self.salts[j]).collect(),
            path: self.tree.generate_proof(indices),
        }
    }
}
