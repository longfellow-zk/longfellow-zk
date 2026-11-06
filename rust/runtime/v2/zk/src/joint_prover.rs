// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Prover ownership of the selected joint commitment and its final equations.
use super::{Bodies, Coefficients, Fields, JointParam, Responses, Statements, Witnesses};
use crate::runtime::{
    random::RandomEngine,
    v2::{
        polygero::joint::Participants,
        proto::polygero::{JointPolygeroProof, PolygeroCommitment},
        transcript::Transcript,
        witness_selection,
    },
};

/// The underlying backend state is inaccessible to frontend callers.
pub struct JointProver<S, C, R> {
    selection: witness_selection::Prover<S, C, R>,
}
impl<L: Fields> JointParam<L> {
    pub fn commit(
        &self,
        witnesses: Witnesses<L>,
        transcript: &mut Transcript,
        rng: &mut impl RandomEngine,
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
            witness_selection::commit(&self.selection, witnesses, transcript, rng)?;
        Ok((JointProver { selection }, root, responses))
    }
}
impl<S, C, R> JointProver<S, C, R> {
    pub fn prove<L: Fields>(
        self,
        param: &JointParam<L>,
        statements: Statements<L>,
        transcript: &mut Transcript,
    ) -> Result<JointPolygeroProof<Bodies<L>>, String>
    where
        L::Selection: witness_selection::Fields<Coefficients = C, Responses = R>,
        <L::Selection as witness_selection::Fields>::Backend: Participants<States = S>,
    {
        self.selection
            .prove(&param.selection, statements, transcript)
    }
}
