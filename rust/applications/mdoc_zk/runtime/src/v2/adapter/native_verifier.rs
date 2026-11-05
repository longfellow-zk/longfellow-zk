// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
impl<const W: usize, F: ZkField<W>> SharedParticipant<W, F> {
    pub fn reduce_verify(
        &self,
        circuit: &Circuit<F>,
        public: &[F::E],
        proof: &SumcheckProof<W, F>,
        t: &mut Transcript,
        f: &F,
    ) -> Result<LinearClaim<F::E>, String> {
        if circuit.id != self.id {
            return Err("shared circuit mismatch".into());
        }
        native_frontend::reduce(circuit, public, proof, t, f)
    }
}
