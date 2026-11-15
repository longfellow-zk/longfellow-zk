// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    algebra::packing::PackingExtension,
    random::PrivateRandom,
    v2::{
        sumcheck::SumcheckPads,
        zk::{
            prover::{prove_values, Identity},
            CircuitInput,
        },
    },
};
impl<F: ZkField + PackingField> PureSplit<F> {
    /// Sample the pads. The participant commits nothing, so it has no
    /// witness for the joint commitment.
    pub(crate) fn prepare(
        &self,
        private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<PureState<'_, F>, String> {
        if private.len() != self.frontend.inputs.committed() {
            return Err("split witness shape".into());
        }
        let f = self.frontend.field();
        let parameters = &self.frontend.backend.parameters;
        let mut values = parameters.extension().into_input_elements(f, private);
        let (pads, suffix) = sumcheck::sample_pads(self.frontend.geometry.sumcheck(), rng, f);
        values.extend(suffix);
        Ok(PureState {
            pads,
            values,
            participant: self.frontend.identity(&self.map),
        })
    }
}
/// Prover state of a pure-foreign participant before its frontend.
pub(crate) struct PureState<'p, F: ZkField + PackingField> {
    pads: SumcheckPads<F>,
    /// `[private inputs | pads]`, in value order.
    values: Vec<F::E>,
    participant: Identity<'p, F, StorageMap>,
}

/// The prover's pure-foreign reduction, with the values of the claim.
pub(crate) struct PurePending<E> {
    pub(crate) claim: PureClaim<E>,
    #[cfg(test)]
    pub(crate) values: Vec<E>,
}

/// Run the pure-foreign frontend of `t`'s part and reduce its constraints to
/// its unbatched rows.
pub(crate) fn prove<F: ZkField + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, F, PureSplit<F>>>,
    state: PureState<'_, F>,
) -> Result<(SumcheckProof<F>, PurePending<F::E>), String> {
    let p = t.part().participant;
    if !p.frontend.prepared(&state.participant, &p.map) {
        return Err("split state belongs to another participant".into());
    }
    let (proof, constraints) = prove_values(t, &state.values, state.pads)?;
    let claim = frontend_claim(t.part(), constraints)?;
    Ok((
        proof,
        PurePending {
            claim,
            #[cfg(test)]
            values: state.values,
        },
    ))
}

impl<F: ZkField + PackingField> PureState<'_, F> {
    pub(crate) fn values(&self) -> &[F::E] {
        &self.values
    }
}
