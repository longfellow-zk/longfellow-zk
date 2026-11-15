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

//! Fiat–Shamir order shared by the prover and verifier.
//!
//! The commitment's `Commitment` message (the root) is the first prover
//! message after the statement; the statement already fixes the joint
//! geometry and every field's source (transcript I1, I3). The caller then
//! runs sumcheck to derive A and b on this same transcript, and hands the
//! statements to the prover's `prove` or the verifier's `reduce`. These draw
//! the batching weights alpha and challenge polynomials B_i first
//! (`weights_for`), at the boundary after the last message every statement
//! depends on, and use them at once; nothing is absorbed of their own:
//! the statements are derived from absorbed messages and challenges, so
//! their digests are not absorbed again. Each field
//! then sends its `PolygeroResponse` (H, Z) before the columns are chosen.
//! Column order is exactly the order returned by `choose`.
use super::{
    joint::{FieldChallenges, JointPolygeroParam},
    PolygeroParam,
};
use crate::{
    core::algebra::{RegisteredField, SerializableField},
    runtime::{
        algebra::SupportsSampling,
        v2::{
            polygero::Participants,
            proto::{
                polygero::{FieldProof, PolygeroCommitment},
                tags::Tag,
            },
            transcript::{Encoder, Message, ProverMessage, Reading, TranscriptRef},
        },
    },
};

/// `Commitment` (32): Bytes(32), the joint Merkle root.
struct CommitmentMessage<'a>(&'a PolygeroCommitment);
impl Message for CommitmentMessage<'_> {
    const TAG: Tag = Tag::Commitment;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(&self.0.root.data);
    }
}
impl ProverMessage for CommitmentMessage<'_> {}

/// `PolygeroResponse` (96): Elements(F, k + s), H on the first k + s oracle
/// nodes; then Elements(F, 2k), Z on the first 2k nodes.
struct ResponseMessage<'a, F: RegisteredField> {
    f: &'a F,
    body: &'a FieldProof<F::E>,
}
impl<F: RegisteredField> Message for ResponseMessage<'_, F> {
    const TAG: Tag = Tag::PolygeroResponse;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, &self.body.h);
        e.elements(self.f, &self.body.z);
    }
}
impl<F: RegisteredField> ProverMessage for ResponseMessage<'_, F> {}

/// Draw one field's batching challenges after the last message every
/// participant statement depends on.
pub(super) fn challenges<F: SupportsSampling + SerializableField>(
    ts: &mut Reading<'_>,
    param: &PolygeroParam,
    nconstraints: usize,
    f: &F,
) -> FieldChallenges<F::E> {
    // Evaluation on any distinct s+1 points is a bijection on degree-at-most-s
    // polynomials, so oracle-prefix samples give the same uniform challenge.

    let alpha = ts.elements(f, nconstraints).collect();
    let batching_samples = param
        .batched_rows()
        .map(|_| ts.elements(f, param.geom.s + 1).collect())
        .collect();
    FieldChallenges {
        alpha,
        batching_samples,
    }
}

pub(super) fn send_response<F: RegisteredField>(
    t: &mut TranscriptRef<'_>,
    body: &FieldProof<F::E>,
    f: &F,
) {
    t.send(&ResponseMessage { f, body });
}

impl<L: Participants> JointPolygeroParam<L> {
    /// Send the root: the first message after the statement.
    pub(super) fn receive(&self, root: &PolygeroCommitment, t: &mut TranscriptRef<'_>) {
        t.send(&CommitmentMessage(root));
    }
    /// Draw every field's batching weights for the equations of
    /// `statements` (transcript I8): per field, one weight per equation, then
    /// s+1 samples per batched row. The prover's `prove` and the verifier's
    /// `reduce` call it on entry, after the last message any statement
    /// depends on, and consume the weights in the same call; they are never
    /// a value of their own.
    pub(super) fn weights_for(
        &self,
        statements: &L::Statements,
        t: &mut TranscriptRef<'_>,
    ) -> L::Challenges {
        // Every participant's statement is fixed before any field's batching
        // challenges: they all follow the last frontend message.
        t.draw(|r| self.participants.challenges(statements, r))
    }
    pub(super) fn queries(&self, b: &L::Bodies, t: &mut TranscriptRef<'_>) -> Vec<usize> {
        // Fix all H/Z responses before drawing the single shared query set.
        // Sharing queries correlates the field checks; it does not merge them.
        self.participants.send_responses(b, t);
        t.draw(|r| {
            let mut indices = vec![0; self.config.t];
            let mut scratch = vec![0; self.config.n];
            r.choose(&mut indices, self.config.n, &mut scratch);
            indices
        })
    }
}
