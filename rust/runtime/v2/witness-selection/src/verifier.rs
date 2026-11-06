// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    polygero::{joint::ReceivedCommitment, JointPolygeroVerifier},
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::Transcript,
};

/// Evidence that the fingerprint and frontend equations were authenticated.
/// This is not complete-proof verification; the enclosing protocol checks its seal.
pub struct Authenticated {
    _private: (),
}

pub struct Verifier<L: Fields> {
    param: Param<L>,
    backend: JointPolygeroVerifier<L::Backend>,
    root: PolygeroCommitment,
    coefficients: L::Coefficients,
    responses: L::Responses,
}
impl<L: Fields> Verifier<L> {
    pub fn receive(
        param: Param<L>,
        root: &PolygeroCommitment,
        responses: L::Responses,
        t: &mut Transcript,
    ) -> Result<Self, String> {
        let received = param.commitment_context().receive(root, t);
        Self::from_received(param, root, &received, responses, t)
    }
    pub fn from_received(
        param: Param<L>,
        root: &PolygeroCommitment,
        received: &ReceivedCommitment,
        responses: L::Responses,
        t: &mut Transcript,
    ) -> Result<Self, String> {
        let backend = JointPolygeroVerifier::from_received(param.backend.clone(), received)
            .map_err(|e| e.to_string())?;
        let coefficients = param.challenges(root, t);
        param.bind_responses(&responses, t);
        Ok(Self {
            param,
            backend,
            root: root.clone(),
            coefficients,
            responses,
        })
    }
    /// Intermediate authentication only; the enclosing complete verifier must
    /// additionally check its mandatory final transcript seal.
    pub fn authenticate(
        self,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
        t: &mut Transcript,
    ) -> Result<Authenticated, String> {
        let statements =
            self.param
                .fields
                .authenticate(statements, self.coefficients, &self.responses)?;
        self.backend
            .reduce(&self.root, proof, &statements, t)
            .map_err(|e| e.to_string())?;
        Ok(Authenticated { _private: () })
    }
}
