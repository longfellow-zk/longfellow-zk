// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    random::RandomEngine,
    v2::{
        polygero::JointPolygeroProver,
        proto::polygero::{JointPolygeroProof, PolygeroCommitment},
        transcript::{Transcript, TranscriptRef},
    },
};

/// Private-witness operations belong to the prover role; shared field lists
/// expose only layout, challenge, and affine-equation operations.
pub trait ProverFields: Fields {
    fn validate_witnesses(&self, witnesses: &Witnesses<Self>) -> Result<(), String>;
    fn append_masks(
        &self,
        witnesses: &mut Witnesses<Self>,
        rng: &mut impl crate::runtime::random::RandomEngine,
    );
    fn responses(
        &self,
        witnesses: &Witnesses<Self>,
        coefficients: &Self::Coefficients,
    ) -> Self::Responses;
}
impl ProverFields for () {
    fn validate_witnesses(&self, _: &()) -> Result<(), String> {
        Ok(())
    }
    fn append_masks(&self, _: &mut (), _: &mut impl crate::runtime::random::RandomEngine) {}
    fn responses(&self, _: &(), _: &()) {}
}
impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
        D: EvaluationDomain<W, F>,
        T: ProverFields,
    > ProverFields for (Field<'a, W, F, D>, T)
{
    fn validate_witnesses(&self, witnesses: &Witnesses<Self>) -> Result<(), String> {
        if witnesses.0.len() != self.0.cells {
            return Err("fingerprint source witness length".into());
        }
        self.1.validate_witnesses(&witnesses.1)
    }
    fn append_masks(
        &self,
        witnesses: &mut Witnesses<Self>,
        rng: &mut impl crate::runtime::random::RandomEngine,
    ) {
        witnesses
            .0
            .extend((0..FINGERPRINTS).map(|_| rng.elt_field(self.0.f)));
        self.1.append_masks(&mut witnesses.1, rng);
    }
    fn responses(
        &self,
        witnesses: &Witnesses<Self>,
        coefficients: &Self::Coefficients,
    ) -> Self::Responses {
        let n = self.0.cells;
        (
            FingerprintResponse {
                values: std::array::from_fn(|j| {
                    let dot = crate::runtime::algebra::blas::dot(
                        &coefficients.0[j],
                        &witnesses.0[..n],
                        self.0.f,
                    );
                    self.0.f.addf(&witnesses.0[n + j], &dot)
                }),
            },
            self.1.responses(&witnesses.1, &coefficients.1),
        )
    }
}

/// The backend handle is private: completing this protocol always appends its
/// affine equations, so callers cannot forget to authenticate the fingerprints.
pub struct Prover<S, C, R> {
    backend: JointPolygeroProver<S>,
    context: Digest,
    coefficients: C,
    responses: R,
}
pub fn commit<L: ProverFields>(
    param: &Param<L>,
    mut witnesses: Witnesses<L>,
    t: Transcript,
    rng: &mut impl RandomEngine,
) -> Result<
    (
        Prover<<L::Backend as BackendParticipants>::States, L::Coefficients, L::Responses>,
        PolygeroCommitment,
        L::Responses,
    ),
    String,
>
where
    Witnesses<L>: Clone,
{
    param.fields.validate_witnesses(&witnesses)?;
    param.fields.append_masks(&mut witnesses, rng);
    // Retain the original cells only through this early exchange. The backend
    // consumes its copy while encoding; no raw witness is retained by Prover.
    let (mut backend, root) =
        JointPolygeroProver::commit(&param.backend, witnesses.clone(), t, rng)
            .map_err(|e| e.to_string())?;
    let coefficients = param.challenges(&root, &mut backend.transcript());
    let responses = param.fields.responses(&witnesses, &coefficients);
    param.absorb_responses(&responses, &mut backend.transcript());
    Ok((
        Prover {
            backend,
            context: param.context(),
            coefficients,
            responses: responses.clone(),
        },
        root,
        responses,
    ))
}
impl<S, C, R> Prover<S, C, R> {
    pub fn transcript(&mut self) -> TranscriptRef<'_> {
        self.backend.transcript()
    }
    pub fn prove<L: Fields<Coefficients = C, Responses = R>>(
        self,
        param: &Param<L>,
        statements: Statements<L>,
    ) -> Result<(JointPolygeroProof<Bodies<L>>, Transcript), String>
    where
        L::Backend: BackendParticipants<States = S>,
    {
        if self.context != param.context() {
            return Err("witness selection parameter mismatch".into());
        }
        let statements =
            param
                .fields
                .authenticate(statements, self.coefficients, &self.responses)?;
        self.backend
            .prove(&param.backend, &statements)
            .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
#[path = "../tests/protocol.rs"]
mod tests;
