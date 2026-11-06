// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::{Bodies, Fields, JointParam, Responses, Statements};
use crate::runtime::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    random::transcript_v2::Transcript,
    witness_selection,
};

/// Intermediate authentication; the complete proof verifier still checks its seal.
pub struct Authenticated {
    _selection: witness_selection::Authenticated,
}

pub struct JointVerifier<L: Fields> {
    selection: witness_selection::Verifier<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub fn receive(
        self,
        root: &PolygeroCommitment,
        responses: Responses<L>,
        transcript: &mut Transcript,
    ) -> Result<JointVerifier<L>, String> {
        Ok(JointVerifier {
            selection: witness_selection::Verifier::receive(
                self.selection,
                root,
                responses,
                transcript,
            )?,
        })
    }
}
impl<L: Fields> JointVerifier<L> {
    pub fn authenticate(
        self,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
        transcript: &mut Transcript,
    ) -> Result<Authenticated, String> {
        Ok(Authenticated {
            _selection: self.selection.authenticate(proof, statements, transcript)?,
        })
    }
}
