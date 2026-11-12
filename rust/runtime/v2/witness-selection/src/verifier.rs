// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    polygero::JointPolygeroVerifier,
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Transcript, TranscriptRef},
};

/// Evidence that the fingerprint and frontend equations were authenticated.
/// This is not complete-proof verification; the enclosing protocol checks its seal.
pub struct Authenticated {
    transcript: Transcript,
}
impl Authenticated {
    /// Release the checked session for the enclosing complete-proof seal.
    pub fn into_transcript(self) -> Transcript {
        self.transcript
    }
}

/// Retains the early fingerprint state while the caller runs the frontend.
/// The backend owns the session through authentication and frontend reduction.
pub struct Verifier<L: Fields> {
    param: Param<L>,
    backend: JointPolygeroVerifier<L::Backend>,
    coefficients: L::Coefficients,
    responses: L::Responses,
}
impl<L: Fields> Verifier<L> {
    pub fn receive(
        param: Param<L>,
        root: &PolygeroCommitment,
        responses: L::Responses,
        t: Transcript,
    ) -> Self {
        let mut backend = JointPolygeroVerifier::new(param.backend.clone(), root, t);
        let coefficients = param.challenges(root, &mut backend.transcript());
        param.absorb_responses(&responses, &mut backend.transcript());
        Self {
            param,
            backend,
            coefficients,
            responses,
        }
    }
    pub fn transcript(&mut self) -> TranscriptRef<'_> {
        self.backend.transcript()
    }
    /// Intermediate authentication only; the enclosing complete verifier must
    /// additionally check its mandatory final transcript seal.
    pub fn authenticate(
        self,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
    ) -> Result<Authenticated, String> {
        let statements =
            self.param
                .fields
                .authenticate(statements, self.coefficients, &self.responses)?;
        let transcript = self
            .backend
            .reduce(proof, &statements)
            .map_err(|e| e.to_string())?;
        Ok(Authenticated { transcript })
    }
}
