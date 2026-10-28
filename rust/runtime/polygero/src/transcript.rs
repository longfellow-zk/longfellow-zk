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

//! Fiat–Shamir ordering shared by the prover and verifier.
//!
//! First bind the context and commitment root. The caller can then run sumcheck
//! to derive A and b on this same transcript. Absorb the caller's statement
//! digest before sampling scalar weights alpha and challenge polynomials B_i,
//! then bind H and Z before choosing columns.
//! Column order is exactly the order returned by `choose`.
//!
//! The commitment context fixes dimensions, product constraints and domain
//! ordering. The later digest binds the source statement from which
//! the caller derives A and b, independently of their sparse representation.
use sha2::{Digest as _, Sha256};

use super::{PolygeroCommitment, PolygeroGeometry, PolygeroParam, PolygeroProductConstraint};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        proto::Digest,
        random::{RandomEngine, Transcript},
    },
};

/// Bind the public layout and commitment root before deriving any challenges.
pub(super) fn receive_commitment(
    ts: &mut Transcript,
    param: &PolygeroParam,
    com: &PolygeroCommitment,
) {
    ts.write_bytes(b"polygero/root/commitment/v1");
    ts.write_bytes(&param.context.data);
    ts.write_bytes(&com.root.data);
}
/// Independent constraint-batching scalars and evaluation-basis polynomial samples.
pub(super) struct Challenges<E> {
    /// Linear equations first, then three copy-equality weights per product.
    pub(super) alpha: Vec<E>,
    /// Uniform evaluations of B_i on the first s+1 nodes of the oracle.
    /// Entry i belongs to W_i; the final row fstar has no batching polynomial.
    pub(super) batching_samples: Vec<Vec<E>>,
}
/// Bind the source statement, then sample challenges for its compiled equations.
/// The caller supplies the same digest to both roles and guarantees that A and b
/// implement that statement. Term ordering and explicit zeros are not hashed.
pub(super) fn challenges<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling + SerializableField,
>(
    ts: &mut Transcript,
    param: &PolygeroParam,
    nconstraints: usize,
    statement: &Digest,
    f: &F,
) -> Challenges<F::E> {
    // Evaluation on any distinct s+1 points is a bijection on degree-at-most-s
    // polynomials, so oracle-prefix samples give the same uniform challenge.
    ts.write_bytes(b"polygero/root/challenges/oracle-basis/v6");
    ts.write_bytes(&statement.data);

    let alpha = ts.elt_field_slice(nconstraints + 3 * param.geom.nq, f);
    let batching_samples = param
        .batched_rows()
        .map(|_| ts.elt_field_slice(param.geom.s + 1, f))
        .collect();
    Challenges {
        alpha,
        batching_samples,
    }
}
/// Bind H and Z, then sample distinct oracle columns in choose() order.
/// Only response samples enter this step; columns and their opening are built
/// afterward and therefore cannot be inputs to their own query selection.
pub(super) fn queries<F: SerializableField>(
    ts: &mut Transcript,
    param: &PolygeroParam,
    h: &[F::E],
    z: &[F::E],
    f: &F,
) -> Vec<usize> {
    ts.write_bytes(b"polygero/root/openings/v1");
    for response in [h, z] {
        ts.write_elt_field_slice(response, f);
    }
    let mut indices = vec![0; param.geom.t];
    ts.choose(&mut indices, param.geom.n, param.geom.t);
    indices
}

/// Bind the point ordering, dimensions and product layout into every
/// column hash and transcript. The byte encoding is independent of FFT machinery.
pub(super) fn context_digest(
    geom: &PolygeroGeometry,
    domain_id: &[u8],
    products: &[PolygeroProductConstraint],
) -> Digest {
    let mut hash = Sha256::new();
    hash.update(b"polygero/root/context/ambient/fstar-last/v11");
    hash.update((geom.k as u64).to_le_bytes());
    hash.update((domain_id.len() as u64).to_le_bytes());
    hash.update(domain_id);
    for size in geom.sizes() {
        hash.update((size as u64).to_le_bytes());
    }
    for product in products {
        for index in [product.x, product.y, product.z] {
            hash.update((index as u64).to_le_bytes());
        }
    }
    Digest {
        data: hash.finalize().into(),
    }
}
