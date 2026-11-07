// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::{Bodies, Fields, JointParam, Responses, Statements};
use crate::runtime::v2::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Transcript, TranscriptRef},
    witness_selection,
};

/// Intermediate authentication; the complete proof verifier still checks its seal.
pub struct Authenticated {
    _selection: witness_selection::Authenticated,
}
impl Authenticated {
    pub fn into_transcript(self) -> Transcript {
        self._selection.into_transcript()
    }
}

/// Own the selected commitment and its session through frontend reduction
/// and final authentication. Late stages cannot supply a different transcript.
pub struct JointVerifier<L: Fields> {
    selection: witness_selection::Verifier<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub fn receive(
        self,
        root: &PolygeroCommitment,
        responses: Responses<L>,
        transcript: Transcript,
    ) -> JointVerifier<L> {
        JointVerifier {
            selection: witness_selection::Verifier::receive(
                self.selection,
                root,
                responses,
                transcript,
            ),
        }
    }
}
impl<L: Fields> JointVerifier<L> {
    pub fn transcript(&mut self) -> TranscriptRef<'_> {
        self.selection.transcript()
    }
    pub fn authenticate(
        self,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
    ) -> Result<Authenticated, String> {
        Ok(Authenticated {
            _selection: self.selection.authenticate(proof, statements)?,
        })
    }
}
