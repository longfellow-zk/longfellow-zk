// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        polygero::{JointPolygeroProver, Participants as BackendParticipants},
        proto::{
            polygero::{JointPolygeroProof, PolygeroCommitment},
            witness_selection::{FingerprintResponse, FINGERPRINTS},
        },
        transcript::{Bound, SessionStamp},
    },
};

/// Private-witness operations belong to the prover role; shared field lists
/// expose only layout, challenge, and affine-equation operations.
pub trait ProverFields: Fields {
    fn validate_witnesses(&self, witnesses: &Witnesses<Self>) -> Result<(), String>;
    fn append_masks(&self, witnesses: &mut Witnesses<Self>, rng: &mut impl PrivateRandom);
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
    fn append_masks(&self, _: &mut (), _: &mut impl PrivateRandom) {}
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
    fn append_masks(&self, witnesses: &mut Witnesses<Self>, rng: &mut impl PrivateRandom) {
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
/// It records the session it committed on and completes only on that session.
pub struct Prover<S, C, R> {
    backend: JointPolygeroProver<S>,
    session: SessionStamp,
    coefficients: C,
    responses: R,
}
/// Commit, draw the fingerprint coefficients and send the responses, all on
/// `t`'s session, before any frontend challenge.
pub fn commit<L: ProverFields>(
    t: &mut Bound<'_, Param<L>>,
    mut witnesses: Witnesses<L>,
    rng: &mut impl PrivateRandom,
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
    let param = t.part();
    param.fields.validate_witnesses(&witnesses)?;
    param.fields.append_masks(&mut witnesses, rng);
    // Retain the original cells only through this early exchange. The backend
    // consumes its copy while encoding; no raw witness is retained by Prover.
    let (backend, root) =
        JointPolygeroProver::commit(&mut t.project(|p| &p.backend), witnesses.clone(), rng)
            .map_err(|e| e.to_string())?;
    let coefficients = param.challenges(&mut t.transcript());
    let responses = param.fields.responses(&witnesses, &coefficients);
    param.send_responses(&responses, &mut t.transcript());
    Ok((
        Prover {
            backend,
            session: t.session(),
            coefficients,
            responses: responses.clone(),
        },
        root,
        responses,
    ))
}
impl<S, C, R> Prover<S, C, R> {
    pub fn prove<L: Fields<Coefficients = C, Responses = R>>(
        self,
        t: &mut Bound<'_, Param<L>>,
        statements: Statements<L>,
    ) -> Result<JointPolygeroProof<Bodies<L>>, String>
    where
        L::Backend: BackendParticipants<States = S>,
    {
        let param = t.part();
        if self.session != t.session() {
            return Err("witness selection session mismatch".into());
        }
        let statements =
            param
                .fields
                .authenticate(statements, self.coefficients, &self.responses)?;
        self.backend
            .prove(&mut t.project(|p| &p.backend), &statements)
            .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests;
