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
//! The commitment context fixes dimensions and domain
//! ordering. The later digest binds the source statement from which
//! the caller derives A and b, independently of their sparse representation.
use sha2::{Digest as _, Sha256};

use super::{
    joint::{JointPolygeroParam, Participants},
    PolygeroCommitment, PolygeroGeometry, PolygeroParam,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::SupportsSampling,
        proto::Digest,
        v2::{
            proto::polygero::FieldProof,
            transcript::{Reading, RoundLabel, TranscriptRef, Writing},
        },
    },
};

/// Independent constraint-batching scalars and evaluation-basis polynomial samples.
pub struct Challenges<E> {
    /// One independent weight per affine equation.
    pub(super) alpha: Vec<E>,
    /// Uniform evaluations of B_i on the first s+1 nodes of the oracle.
    /// Entry i belongs to W_i; the final row fstar has no batching polynomial.
    pub(super) batching_samples: Vec<Vec<E>>,
}
/// Sample after the joint binding pass has fixed every participant statement.
/// A reading capability cannot absorb another message or open another round.
pub(super) fn challenges<F: SupportsSampling + SerializableField>(
    ts: &mut Reading<'_>,
    param: &PolygeroParam,
    nconstraints: usize,
    f: &F,
) -> Challenges<F::E> {
    // Evaluation on any distinct s+1 points is a bijection on degree-at-most-s
    // polynomials, so oracle-prefix samples give the same uniform challenge.

    let alpha = ts.elt_field_slice(nconstraints, f);
    let batching_samples = param
        .batched_rows()
        .map(|_| ts.elt_field_slice(param.geom.s + 1, f))
        .collect();
    Challenges {
        alpha,
        batching_samples,
    }
}
/// Bind the point ordering and dimensions into every
/// column hash and transcript. The byte encoding is independent of FFT machinery.
pub(super) fn context_digest(geom: &PolygeroGeometry, domain_id: &[u8]) -> Digest {
    let mut hash = Sha256::new();
    hash.update(b"polygero/root/context/linear/v1");
    hash.update((domain_id.len() as u64).to_le_bytes());
    hash.update(domain_id);
    for size in geom.sizes() {
        hash.update((size as u64).to_le_bytes());
    }
    Digest {
        data: hash.finalize().into(),
    }
}

// Tuple traversal lives in joint; all transcript framing and round transitions
// live here, shared by both roles. Binding completes before squeezing begins.
pub(super) fn bind_statement(
    t: &mut Writing<'_>,
    digest: &Digest,
    context: &Digest,
    nconstraints: usize,
) {
    t.write_bytes(&digest.data);
    t.write_bytes(&context.data);
    t.write_bytes(&(nconstraints as u64).to_le_bytes());
}

pub(super) fn bind_response<F: SerializableField>(
    t: &mut Writing<'_>,
    body: &FieldProof<F::E>,
    f: &F,
) {
    t.write_elt_field_slice(&body.h, f);
    t.write_elt_field_slice(&body.z, f);
}

impl<L: Participants> JointPolygeroParam<L> {
    pub(super) fn receive(&self, root: &PolygeroCommitment, t: &mut TranscriptRef<'_>) {
        t.bind(|w| {
            w.write_bytes(b"polygero/joint/root/v1");
            w.write_bytes(&self.context.data);
        });
        t.bind(|w| w.write_bytes(&root.root.data));
    }
    pub(super) fn challenges(&self, s: &L::Statements, t: &mut TranscriptRef<'_>) -> L::Challenges {
        // Complete the binding pass first: a later field's statement must not
        // be chosen after seeing an earlier field's batching challenges.
        t.round(RoundLabel::Batching, |mut w| {
            self.participants.bind_statements(s, &mut w);
            let mut r = w.begin_squeeze();
            let challenges = self.participants.challenges(s, &mut r);
            r.end_round(challenges)
        })
    }
    pub(super) fn queries(&self, b: &L::Bodies, t: &mut TranscriptRef<'_>) -> Vec<usize> {
        // Fix all H/Z responses before sampling the single shared query set.
        // Sharing queries correlates the field checks; it does not merge them.
        t.round(RoundLabel::Opening, |mut w| {
            self.participants.bind_responses(b, &mut w);
            let mut r = w.begin_squeeze();
            let mut indices = vec![0; self.config.t];
            r.choose(&mut indices, self.config.n, self.config.t);
            r.end_round(indices)
        })
    }
}
