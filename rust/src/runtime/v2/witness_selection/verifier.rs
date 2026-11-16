// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    polygero::{JointPolygeroVerifier, VerifierParticipants},
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, SessionStamp},
};

/// Evidence that the fingerprint and frontend equations were authenticated.
/// This is not complete-proof verification; the enclosing protocol checks its seal.
pub(crate) struct Authenticated {
    _private: (),
}

/// The field lists a verifier checks: those whose backend participants check
/// their openings.
pub(crate) trait VerifierFields: Fields<Backend: VerifierParticipants> {}
impl VerifierFields for () {}
impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + RegisteredField + SupportsSampling,
        D: EvaluationDomain<W, F>,
        T: VerifierFields,
    > VerifierFields for (Field<'a, W, F, D>, T)
{
}

/// Retains the early fingerprint state while the caller runs the frontend.
/// It records the session that received the commitment and authenticates
/// only on that session.
pub(crate) struct Verifier<L: Fields> {
    backend: JointPolygeroVerifier<L::Backend>,
    session: SessionStamp,
    coefficients: L::Coefficients,
    responses: L::Responses,
}
impl<L: VerifierFields> Verifier<L> {
    /// Receive the root, draw the coefficients and absorb the responses on
    /// `t`'s session: the same schedule as `commit`.
    pub(crate) fn receive(
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
    /// Check the opening on the session that received the commitment
    /// against `statements`, the frontend equations of every field, derived
    /// on this session, each followed by its fingerprint equations, which
    /// this attaches from the coefficients and responses of the commitment;
    /// the backend then draws its batching weights at the current boundary.
    /// Intermediate authentication only; the enclosing complete verifier must
    /// additionally check its mandatory final transcript seal. Only the joint
    /// ZK verifier calls it (`JointVerifier::finish`).
    pub(crate) fn finish(
        self,
        t: &mut Bound<'_, Param<L>>,
        statements: Statements<L>,
        proof: &JointPolygeroProof<Bodies<L>>,
    ) -> Result<Authenticated, String> {
        let param = t.part();
        if self.session != t.session() {
            return Err("witness selection session mismatch".into());
        }
        let augmented = param.fields.authenticate(
            statements,
            self.coefficients,
            &self.responses,
            &self.session,
        )?;
        self.backend
            .reduce(&mut t.project(|p| &p.backend), augmented, proof)
            .map_err(|e| e.to_string())?;
        Ok(Authenticated { _private: () })
    }
}
