// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::random::RandomEngine;
impl<const W: usize, F: ZkField<W>> SharedParticipant<W, F> {
    pub fn prepare(
        &self,
        circuit: &Circuit<F>,
        private: Vec<F::E>,
        mask: F::E,
        rng: &mut impl RandomEngine,
        f: &F,
    ) -> Result<(SharedState<W, F>, Vec<F::E>), String> {
        if circuit.id != self.id {
            return Err("shared circuit mismatch".into());
        }
        let prepared = native_frontend::prepare(circuit, private, rng, f)?;
        let mut witness = prepared.values[self.shared..self.private].to_vec();
        witness.push(mask.clone());
        witness.extend_from_slice(&prepared.values[self.private..]);
        Ok((
            SharedState {
                prepared,
                mask,
                shared: self.shared,
                id: self.id,
                config: self.config,
            },
            witness,
        ))
    }
    pub fn reduce(
        &self,
        circuit: &Circuit<F>,
        public: &[F::E],
        state: SharedState<W, F>,
        t: &mut Transcript,
        f: &F,
    ) -> Result<SharedReduction<W, F>, String> {
        if state.id != self.id || state.config != self.config || state.shared != self.shared {
            return Err("shared state ownership".into());
        }
        let values = state.prepared.values[..self.shared].to_vec();
        let (proof, claim) = native_frontend::prove(circuit, public, state.prepared, t, f)?;
        Ok(SharedReduction {
            proof,
            claim,
            values,
            mask: state.mask,
        })
    }
}

pub(in crate::mdoc::runtime::v2) struct SharedState<const W: usize, F: ZkField<W>> {
    prepared: native_frontend::Prepared<W, F>,
    mask: F::E,
    shared: usize,
    id: [u8; 32],
    config: PolygeroConfig,
}
pub(in crate::mdoc::runtime::v2) struct SharedReduction<const W: usize, F: ZkField<W>> {
    pub proof: SumcheckProof<W, F>,
    pub claim: LinearClaim<F::E>,
    pub values: Vec<F::E>,
    pub mask: F::E,
}
impl<const W: usize, F: ZkField<W>> SharedReduction<W, F> {
    pub fn masked_value(&self, eta: &F::E, f: &F) -> F::E {
        f.addf(
            &f.mulf(
                eta,
                &crate::runtime::algebra::blas::dot(
                    &self.claim.weights[..self.values.len()],
                    &self.values,
                    f,
                ),
            ),
            &self.mask,
        )
    }
}
