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
use crate::runtime::polygero::PolygeroVerifier;
pub struct PackedVerifier {
    protocol: PackedCircuit,
    geometry: ZkProofGeometry,
    polygero: PolygeroVerifier,
}
impl PackedVerifier {
    pub fn new<D: EvaluationDomain<2, F>>(
        protocol: PackedCircuit,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<Self, String> {
        let (geometry, param) = protocol.prepare(ctx)?;
        Ok(Self {
            protocol,
            geometry,
            polygero: PolygeroVerifier::new(param),
        })
    }
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }
    pub fn receive_commitment(&mut self, proof: &PackedZkProof, t: &mut Transcript) {
        self.protocol.bind_commitment(t);
        self.polygero.receive_commitment(&proof.com, t);
    }
    pub fn verify<D: EvaluationDomain<2, F>>(
        &self,
        public: &[E],
        extra: &[AuxiliaryBitClaim],
        proof: &PackedZkProof,
        t: &mut Transcript,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<(), String> {
        #[cfg(feature = "bench-profile")]
        let mut profile = crate::util::profile::Timer::new("hash.verifier.gkr_and_statement");
        self.protocol.validate(public, extra)?;
        proof
            .sumcheck_proof
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        proof
            .com_proof
            .validate(&self.geometry.com_geom)
            .map_err(|e| e.to_string())?;
        self.protocol.bind_statement(public, extra, t, ctx.f);
        let constraints = sumcheck_v2::derive_constraints(
            &self.protocol.circuit,
            &proof.sumcheck_proof,
            t,
            ctx.f,
        )?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.verifier.claim_combination");
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.protocol.layout.gkr_start);
        let claim = self
            .protocol
            .claim(&constraints, public, extra, &pads, t, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.verifier.ring_switch");
        let reduced = crate::runtime::ring_switch::verifier::reduce(
            &self.protocol.basis,
            &claim,
            &proof.ring_proof,
            &self.protocol.contract,
            t,
            ctx.f,
        )?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.verifier.constraints");
        let statement = super::super::transcript::statement_digest(t);
        let (a, b) = self
            .protocol
            .compile(&constraints, public, &pads, &reduced, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next("hash.verifier.backend_and_cleanup");
        self.polygero
            .verify(
                &b,
                &proof.com,
                &proof.com_proof,
                &a,
                &statement,
                t,
                ctx.domain,
                ctx.f,
            )
            .map_err(|e| e.to_string())
    }
}
