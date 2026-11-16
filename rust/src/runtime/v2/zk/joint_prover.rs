// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prover ownership of the selected joint commitment and its final equations.
use super::joint::JointParam;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        polygero::ProverParticipants,
        proto::polygero::{JointPolygeroProof, PolygeroCommitment},
        transcript::{Bound, Transcript},
        witness_selection::{self, Bodies, ProverFields, Statements, Witnesses},
    },
};

/// The witness-selection prover state of the field list `L`.
type Selection<L> = witness_selection::Prover<
    <<L as witness_selection::Fields>::Backend as ProverParticipants>::States,
    <L as witness_selection::Fields>::Coefficients,
    <L as witness_selection::Fields>::Responses,
>;

/// Owns the parameter and the session from the commitment through the
/// opening, so the opening uses the parameter that committed. The underlying
/// backend state is inaccessible to frontend callers.
pub(crate) struct JointProver<L: ProverFields> {
    param: JointParam<L>,
    transcript: Transcript,
    selection: Selection<L>,
}
impl<L: ProverFields> JointParam<L> {
    pub(crate) fn commit(
        self,
        witnesses: Witnesses<L>,
        mut transcript: Transcript,
        rng: &mut impl PrivateRandom,
    ) -> Result<(JointProver<L>, PolygeroCommitment, L::Responses), String> {
        let (selection, root, responses) =
            witness_selection::commit(&mut transcript.bound(&self.selection), witnesses, rng)?;
        Ok((
            JointProver {
                param: self,
                transcript,
                selection,
            },
            root,
            responses,
        ))
    }
}
impl<L: ProverFields> JointProver<L> {
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
    pub(crate) fn finish(
        self,
        equations: Statements<L>,
    ) -> Result<(JointPolygeroProof<Bodies<L>>, Transcript), String> {
        let Self {
            param,
            mut transcript,
            selection,
        } = self;
        let proof = selection.finish(&mut transcript.bound(&param.selection), equations)?;
        Ok((proof, transcript))
    }
}
