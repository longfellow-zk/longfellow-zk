// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::joint::{Bodies, Fields, JointParam, Responses, Statements};
use crate::runtime::v2::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, Transcript},
    witness_selection,
};

/// Intermediate authentication; the complete proof verifier still checks its seal.
pub(crate) struct Authenticated {
    transcript: Transcript,
    _selection: witness_selection::Authenticated,
}
impl Authenticated {
    pub(crate) fn into_transcript(self) -> Transcript {
        self.transcript
    }
}

/// Own the selected commitment and its session through frontend reduction
/// and final authentication. Late stages cannot supply a different transcript.
pub(crate) struct JointVerifier<L: Fields> {
    param: JointParam<L>,
    transcript: Transcript,
    selection: witness_selection::Verifier<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub(crate) fn receive(
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
    /// Check the opening `proof` against `equations`, each field's frontend
    /// equations, derived on this session, in participant order (for mdoc,
    /// the host's, then the split participant's). Call it right after the
    /// last frontend message of every participant. It consumes the session:
    /// it rejects equations derived on another session, attaches each field's
    /// fingerprint equations, draws the Polygero batching weights at the
    /// current boundary (transcript I8), absorbs each field's response, draws
    /// the columns and checks the opening. The caller still checks the
    /// complete proof's seal on the returned transcript.
    ///
    /// It takes every field's equations, in their types: a list without the
    /// split participant's, or none, does not compile.
    pub(crate) fn finish(
        mut self,
        equations: Statements<L>,
        proof: &JointPolygeroProof<Bodies<L>>,
    ) -> Result<Authenticated, String> {
        let selection = self.selection.finish(
            &mut self.transcript.bound(&self.param.selection),
            equations,
            proof,
        )?;
        Ok(Authenticated {
            transcript: self.transcript,
            _selection: selection,
        })
    }
}
