// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::joint::{Batched, Bodies, Fields, JointParam, Responses, Statements};
use crate::runtime::v2::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, Challenge, Transcript},
    witness_selection,
};

/// Intermediate authentication; the complete proof verifier still checks its seal.
pub struct Authenticated {
    transcript: Transcript,
    _selection: witness_selection::Authenticated,
}
impl Authenticated {
    pub fn into_transcript(self) -> Transcript {
        self.transcript
    }
}

/// Own the selected commitment and its session through frontend reduction
/// and final authentication. Late stages cannot supply a different transcript.
pub struct JointVerifier<L: Fields> {
    param: JointParam<L>,
    transcript: Transcript,
    selection: witness_selection::Verifier<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub fn receive(
        self,
        root: &PolygeroCommitment,
        responses: Responses<L>,
        mut transcript: Transcript,
    ) -> JointVerifier<L> {
        let selection = witness_selection::Verifier::receive(
            &mut transcript.bound(&self.selection),
            root,
            responses,
        );
        JointVerifier {
            param: self,
            transcript,
            selection,
        }
    }
}
impl<L: Fields> JointVerifier<L> {
    /// The owned session, for tests that read it directly.
    #[cfg(test)]
    pub(crate) fn transcript(&mut self) -> crate::runtime::v2::transcript::TranscriptRef<'_> {
        self.transcript.borrow()
    }
    /// The owned session, bound to the statement part a frontend reads.
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        self.transcript.bound(part)
    }
    /// Draw the Polygero batching weights of `statements` after the last
    /// frontend message of every participant (transcript I8). The weights
    /// take the statements with them: `authenticate` accepts them only if no
    /// message was sent since, and checks the opening against the statements
    /// they carry, so no other system can be substituted.
    ///
    /// ```compile_fail,E0061
    /// use longfellow_zk::runtime::v2::{
    ///     proto::polygero::JointPolygeroProof,
    ///     zk::{
    ///         joint::{Bodies, Fields, Statements},
    ///         JointVerifier,
    ///     },
    /// };
    /// fn substitute<L: Fields>(
    ///     mut v: JointVerifier<L>,
    ///     drawn: Statements<L>,
    ///     other: Statements<L>,
    ///     proof: &JointPolygeroProof<Bodies<L>>,
    /// ) {
    ///     let batch = v.weights(drawn);
    ///     let _ = v.authenticate(batch, proof, other);
    /// }
    /// ```
    pub fn weights(&mut self, statements: Statements<L>) -> Challenge<Batched<L>> {
        witness_selection::Param::weights(
            &mut self.transcript.bound(&self.param.selection),
            statements,
        )
    }
    pub fn authenticate(
        mut self,
        batch: Challenge<Batched<L>>,
        proof: &JointPolygeroProof<Bodies<L>>,
    ) -> Result<Authenticated, String> {
        let selection = self.selection.authenticate(
            &mut self.transcript.bound(&self.param.selection),
            batch,
            proof,
        )?;
        Ok(Authenticated {
            transcript: self.transcript,
            _selection: selection,
        })
    }
}
