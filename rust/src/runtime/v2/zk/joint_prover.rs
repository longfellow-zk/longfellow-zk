// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prover ownership of the selected joint commitment and its final equations.
use super::joint::{
    Batched, Bodies, Coefficients, Fields, JointParam, Responses, Statements, Witnesses,
};
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        polygero::Participants,
        proto::polygero::{JointPolygeroProof, PolygeroCommitment},
        transcript::{Bound, Challenge, Transcript},
        witness_selection,
    },
};

/// Owns the session from the commitment through the opening. The underlying
/// backend state is inaccessible to frontend callers.
pub struct JointProver<S, C, R> {
    transcript: Transcript,
    selection: witness_selection::Prover<S, C, R>,
}
impl<L: Fields> JointParam<L> {
    pub fn commit(
        &self,
        witnesses: Witnesses<L>,
        mut transcript: Transcript,
        rng: &mut impl PrivateRandom,
    ) -> Result<
        (
            JointProver<
                <<L::Selection as witness_selection::Fields>::Backend as Participants>::States,
                Coefficients<L>,
                Responses<L>,
            >,
            PolygeroCommitment,
            Responses<L>,
        ),
        String,
    >
    where
        L::Selection: witness_selection::ProverFields,
        Witnesses<L>: Clone,
    {
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
    /// Draw the Polygero batching weights of `statements` after the last
    /// frontend message of every participant (transcript I8). The weights
    /// take the statements with them: `prove` accepts them only if no
    /// message was sent since, and opens the statements they carry.
    pub fn weights<L: Fields>(
        &mut self,
        param: &JointParam<L>,
        statements: Statements<L>,
    ) -> Challenge<Batched<L>> {
        witness_selection::Param::weights(&mut self.transcript.bound(&param.selection), statements)
    }
    pub fn prove<L: Fields>(
        mut self,
        param: &JointParam<L>,
        batch: Challenge<Batched<L>>,
    ) -> Result<(JointPolygeroProof<Bodies<L>>, Transcript), String>
    where
        L::Selection: witness_selection::Fields<Coefficients = C, Responses = R>,
        <L::Selection as witness_selection::Fields>::Backend: Participants<States = S>,
    {
        let proof = self
            .selection
            .prove(&mut self.transcript.bound(&param.selection), batch)?;
        Ok((proof, self.transcript))
    }
}
