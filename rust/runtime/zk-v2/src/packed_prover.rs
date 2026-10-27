// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use crate::{
    core::bits::PackedBits,
    runtime::{
        algebra::Subfield, dual_packing::prover::DualPackingMaskValues, polygero::PolygeroProver,
        proto::polygero::PolygeroCommitment, sumcheck_v2::SumcheckProof,
    },
};
/// Owns the private bits used by both commitment and numerical GKR.
pub struct PackedCommitment {
    bits: PackedBits,
    caller: Vec<E>,
    masks: DualPackingMaskValues,
    pads: SumcheckProof<2, F>,
    polygero: PolygeroProver<2, F>,
    commitment: PolygeroCommitment,
    circuit_id: [u8; 32],
    contract: [u8; 32],
}
impl PackedCircuit {
    pub fn commit<D: EvaluationDomain<2, F>, R: RandomEngine, SF: Subfield<E = E>>(
        &self,
        bits: PackedBits,
        caller: Vec<E>,
        ctx: &ZkContext<'_, 2, F, D>,
        t: &mut Transcript,
        rng: &mut R,
        sf: &SF,
    ) -> Result<(PackedCommitment, ZkProofGeometry), String> {
        if bits.len() != self.layout.private_bits || caller.len() != self.layout.caller_auxiliary {
            return Err("packed witness shape mismatch".into());
        }
        let (geometry, param) = self.prepare(ctx)?;
        let masks = DualPackingMaskValues::sample(rng, ctx.f);
        let (pads, flat) = sumcheck_v2::sample_pads(&geometry.sc_geom, rng, ctx.f);
        let mut witness = crate::runtime::dual_packing::field::pack(&bits);
        witness.extend_from_slice(&caller);
        witness.extend(masks.cells());
        witness.extend(flat);
        self.bind_commitment(t);
        let (polygero, commitment) =
            PolygeroProver::commit(0, witness, param, t, ctx.domain, rng, ctx.f, sf)
                .map_err(|e| e.to_string())?;
        Ok((
            PackedCommitment {
                bits,
                caller,
                masks,
                pads,
                polygero,
                commitment,
                circuit_id: self.circuit.id,
                contract: self.contract,
            },
            geometry,
        ))
    }
    pub fn prove<D: EvaluationDomain<2, F>>(
        &self,
        public: &[E],
        extra: &[AuxiliaryBitClaim],
        state: PackedCommitment,
        t: &mut Transcript,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<PackedZkProof, String> {
        #[cfg(feature = "bench-profile")]
        let mut profile = crate::util::profile::Timer::new("hash.prover.gkr_and_statement");
        self.validate(public, extra)?;
        if state.circuit_id != self.circuit.id
            || state.contract != self.contract
            || state.caller.len() != self.layout.caller_auxiliary
        {
            return Err("packed commitment belongs to a different circuit contract".into());
        }
        let geometry = sumcheck_v2::SumcheckProofGeometry::from_circuit(&self.circuit);
        state.pads.validate(&geometry).map_err(|e| e.to_string())?;
        self.bind_statement(public, extra, t, ctx.f);
        let mut inputs = public.to_vec();
        inputs.extend((0..state.bits.len()).map(|i| E::from(u128::from(state.bits.get(i)))));
        let (sumcheck_proof, constraints) = if let Some(window) = self.boolean_window {
            sumcheck_v2::boolean::prove_core(inputs, &state.pads, &self.circuit, t, ctx.f, window)?
        } else {
            let layers = sumcheck_v2::eval_circuit(inputs, &self.circuit, ctx.f)?;
            sumcheck_v2::prove_core(layers, &state.pads, &self.circuit, t, ctx.f)
        };
        #[cfg(feature = "bench-profile")]
        profile.next("hash.prover.claim_combination");
        let pads = geometry.pad_layout(self.layout.gkr_start);
        let claim = self.claim(&constraints, public, extra, &pads, t, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.prover.dual_packing");
        let (dual_packing_proof, reduced) = crate::runtime::dual_packing::prover::reduce(
            &self.basis,
            &claim,
            &state.bits,
            state.masks,
            &self.contract,
            t,
            ctx.f,
        )?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.prover.constraints");
        let statement = super::super::transcript::statement_digest(t);
        let (a, b) = self.compile(&constraints, public, &pads, &reduced, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.prover.backend_and_cleanup");
        let com_proof = state
            .polygero
            .prove(&b, t, &a, &statement, ctx.domain, ctx.f)
            .map_err(|e| e.to_string())?;
        Ok(PackedZkProof {
            sumcheck_proof,
            dual_packing_proof,
            com: state.commitment,
            com_proof,
        })
    }
}
