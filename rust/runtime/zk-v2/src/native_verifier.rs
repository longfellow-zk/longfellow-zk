// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub(crate) fn reduce<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    public: &[F::E],
    proof: &SumcheckProof<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<LinearClaim<F::E>, String> {
    if f.is_binary() {
        return Err("native claim requires a prime field".into());
    }
    sumcheck_v2::circuit_geometry(&[circuit])?;
    proof
        .validate(&SumcheckProofGeometry::from_circuit(circuit))
        .map_err(|e| e.to_string())?;
    if public.len() != circuit.raw.npublic_input {
        return Err("native frontend public input shape".into());
    }
    transcript.write_sumcheck_statement(circuit, public, f);
    let constraints = sumcheck_v2::derive_constraints(circuit, proof, transcript, f)?;
    batch(circuit, public, constraints, transcript, f)
}
