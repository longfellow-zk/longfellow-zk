// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub(crate) fn reduce<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    public: &[F::E],
    proof: &SumcheckProof<W, F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<LinearClaim<F::E>, String> {
    if f.is_binary() {
        return Err("prime claim requires a prime field".into());
    }
    let geometry = sumcheck::circuit_geometry(&[circuit])?;
    proof.validate(&geometry).map_err(|e| e.to_string())?;
    if public.len() != circuit.raw.npublic_input {
        return Err("prime frontend public input shape".into());
    }
    transcript.write_sumcheck_statement(circuit, public, f);
    let constraints = sumcheck::derive_constraints(circuit, proof, transcript, f)?;
    row_batching::batch(circuit, public, constraints, transcript, f)
}
