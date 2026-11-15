// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    polygero::JointPolygeroVerifier,
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, SessionStamp},
};

/// Evidence that the fingerprint and frontend equations were authenticated.
/// This is not complete-proof verification; the enclosing protocol checks its seal.
pub struct Authenticated {
    _private: (),
}

/// Retains the early fingerprint state while the caller runs the frontend.
/// It records the session that received the commitment and authenticates
/// only on that session.
pub struct Verifier<L: Fields> {
    backend: JointPolygeroVerifier<L::Backend>,
    session: SessionStamp,
    coefficients: L::Coefficients,
    responses: L::Responses,
}
impl<L: Fields> Verifier<L> {
    /// Receive the root, draw the coefficients and absorb the responses on
    /// `t`'s session: the same schedule as `commit`.
    pub fn receive(
        t: &mut Bound<'_, Param<L>>,
        root: &PolygeroCommitment,
        responses: L::Responses,
    ) -> Self {
        let param = t.part();
        let backend = JointPolygeroVerifier::receive(&mut t.project(|p| &p.backend), root);
        let coefficients = param.challenges(&mut t.transcript());
        param.send_responses(&responses, &mut t.transcript());
        Self {
            backend,
            session: t.session(),
            coefficients,
            responses,
        }
    }
    /// Intermediate authentication only; the enclosing complete verifier must
    /// additionally check its mandatory final transcript seal.
    pub fn authenticate(
        self,
        t: &mut Bound<'_, Param<L>>,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
    ) -> Result<Authenticated, String> {
        let param = t.part();
        if self.session != t.session() {
            return Err("witness selection session mismatch".into());
        }
        let statements =
            param
                .fields
                .authenticate(statements, self.coefficients, &self.responses)?;
        self.backend
            .reduce(&mut t.project(|p| &p.backend), proof, &statements)
            .map_err(|e| e.to_string())?;
        Ok(Authenticated { _private: () })
    }
}
