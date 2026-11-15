// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::joint::{Bodies, Fields, JointParam, Responses, Statements};
use crate::runtime::v2::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, Transcript, TranscriptRef},
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
    pub fn transcript(&mut self) -> TranscriptRef<'_> {
        self.transcript.borrow()
    }
    /// The owned session, bound to the statement part a frontend reads.
    pub fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        self.transcript.bound(part)
    }
    pub fn authenticate(
        mut self,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
    ) -> Result<Authenticated, String> {
        let selection = self.selection.authenticate(
            &mut self.transcript.bound(&self.param.selection),
            proof,
            statements,
        )?;
        Ok(Authenticated {
            transcript: self.transcript,
            _selection: selection,
        })
    }
}
