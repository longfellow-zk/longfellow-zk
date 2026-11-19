// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Verifier ownership of early selection and final joint authentication.
use super::joint::JointParam;
use crate::runtime::v2::{
    proto::polygero::{JointPolygeroProof, PolygeroCommitment},
    transcript::{Bound, Transcript, Unverified, VerifiedProof},
    witness_selection::{self, Bodies, Fields, Statements, VerifierFields},
};

/// Evidence that a joint opening authenticated every frontend equation on
/// the verifier's session. It keeps the session and the complete proof whose
/// opening it checked. It is not complete verification: only its
/// `check_seal`, which consumes both, turns that proof into a
/// `VerifiedProof` (zk I7, transcript I10).
pub(crate) struct Authenticated<'a, P> {
    transcript: Transcript,
    proof: Unverified<'a, P>,
    _selection: witness_selection::Authenticated,
}
impl<P> Authenticated<'_, P> {
    /// Check the seal of the complete proof whose opening this authenticated,
    /// on the authenticated session (transcript I10).
    pub(crate) fn check_seal(self) -> Result<VerifiedProof, &'static str> {
        self.transcript.check_seal(self.proof)
    }
    /// The authenticated session, for tests that read it directly.
    #[cfg(test)]
    pub(crate) fn into_transcript(self) -> Transcript {
        self.transcript
    }
}

/// A complete proof, which holds the joint opening `JointVerifier::finish`
/// checks.
pub(crate) trait JointOpening<B> {
    fn opening(&self) -> &JointPolygeroProof<B>;
}
/// A bare opening, for tests that check one without a complete proof.
#[cfg(test)]
impl<B> JointOpening<B> for JointPolygeroProof<B> {
    fn opening(&self) -> &JointPolygeroProof<B> {
        self
    }
}
/// A borrowed proof, for tests that check one they keep.
#[cfg(test)]
impl<B, P: JointOpening<B>> JointOpening<B> for &P {
    fn opening(&self) -> &JointPolygeroProof<B> {
        (**self).opening()
    }
}

/// Own the selected commitment and its session through frontend reduction
/// and final authentication. Late stages cannot supply a different transcript.
pub(crate) struct JointVerifier<L: Fields> {
    param: JointParam<L>,
    transcript: Transcript,
    selection: witness_selection::Verifier<L>,
}
impl<L: Fields> JointParam<L> {
    pub(crate) fn receive(
        self,
        root: &PolygeroCommitment,
        responses: L::Responses,
        mut transcript: Transcript,
    ) -> JointVerifier<L>
    where
        L: VerifierFields,
    {
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
    /// Check the joint opening of `proof`, the complete proof, against
    /// `equations`, each field's frontend
    /// equations, derived on this session, in participant order (for mdoc,
    /// the host's, then the split participant's). Call it right after the
    /// last frontend message of every participant. It consumes the session:
    /// it rejects equations derived on another session, attaches each field's
    /// fingerprint equations, draws the Polygero batching weights at the
    /// current boundary (transcript I8), absorbs each field's response, draws
    /// the columns and checks the opening. The caller still checks the seal
    /// of `proof`, which the returned `Authenticated` keeps
    /// (`Authenticated::check_seal`).
    ///
    /// It takes every field's equations, in their types: a list without the
    /// split participant's, or none, does not compile.
    pub(crate) fn finish<'a, P: JointOpening<Bodies<L>>>(
        mut self,
        equations: Statements<L>,
        proof: Unverified<'a, P>,
    ) -> Result<Authenticated<'a, P>, String>
    where
        L: VerifierFields,
    {
        let selection = self.selection.finish(
            &mut self.transcript.bound(&self.param.selection),
            equations,
            proof.opening(),
        )?;
        Ok(Authenticated {
            transcript: self.transcript,
            proof,
            _selection: selection,
        })
    }
}
