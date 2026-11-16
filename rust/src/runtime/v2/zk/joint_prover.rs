// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prover ownership of the selected joint commitment and its final equations.
use super::joint::JointParam;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        polygero::ProverParticipants,
        proto::polygero::{JointPolygeroProof, PolygeroCommitment},
        transcript::{Bound, Transcript},
        witness_selection::{self, Bodies, Fields, ProverFields, Statements, Witnesses},
    },
};

/// Owns the session from the commitment through the opening. The underlying
/// backend state is inaccessible to frontend callers.
pub(crate) struct JointProver<S, C, R> {
    transcript: Transcript,
    selection: witness_selection::Prover<S, C, R>,
}
impl<L: ProverFields> JointParam<L> {
    pub(crate) fn commit(
        &self,
        witnesses: Witnesses<L>,
        mut transcript: Transcript,
        rng: &mut impl PrivateRandom,
    ) -> Result<
        (
            JointProver<<L::Backend as ProverParticipants>::States, L::Coefficients, L::Responses>,
            PolygeroCommitment,
            L::Responses,
        ),
        String,
    > {
        let (selection, root, responses) =
            witness_selection::commit(&mut transcript.bound(&self.selection), witnesses, rng)?;
        Ok((
            JointProver {
                transcript,
                selection,
            },
            root,
            responses,
        ))
    }
}
impl<S, C, R> JointProver<S, C, R> {
    /// The owned session, for tests that read it directly.
    #[cfg(test)]
    pub(crate) fn transcript(&mut self) -> crate::runtime::v2::transcript::TranscriptRef<'_> {
        self.transcript.borrow()
    }
    /// The owned session, bound to the statement part a frontend reads.
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        self.transcript.bound(part)
    }
    /// Complete the opening with `equations`, each field's frontend
    /// equations, derived on this session, in participant order (for mdoc,
    /// the host's, then the split participant's). Call it right after the
    /// last frontend message of every participant. It consumes the session:
    /// it rejects equations derived on another session, attaches each field's
    /// fingerprint equations, draws the Polygero batching weights at the
    /// current boundary (transcript I8), sends each field's response, draws
    /// the columns and returns the opening with the transcript.
    pub(crate) fn finish<L: Fields<Coefficients = C, Responses = R>>(
        mut self,
        param: &JointParam<L>,
        equations: Statements<L>,
    ) -> Result<(JointPolygeroProof<Bodies<L>>, Transcript), String>
    where
        L::Backend: ProverParticipants<States = S>,
    {
        let proof = self
            .selection
            .finish(&mut self.transcript.bound(&param.selection), equations)?;
        Ok((proof, self.transcript))
    }
}
