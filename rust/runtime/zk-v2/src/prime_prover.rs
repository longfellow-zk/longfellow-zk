// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub(crate) struct Prepared<const W: usize, F: RuntimeField<W> + SerializableField> {
    circuit_id: [u8; 32],
    pads: SumcheckProof<W, F>,
    /// Prime private inputs followed by round pads and independent terminal cells.
    pub values: Vec<F::E>,
}

pub(crate) fn prepare<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    R: crate::runtime::random::RandomEngine,
>(
    circuit: &Circuit<F>,
    private: Vec<F::E>,
    rng: &mut R,
    f: &F,
) -> Result<Prepared<W, F>, String> {
    if f.is_binary() {
        return Err("prime claim requires a prime field".into());
    }
    sumcheck_v2::circuit_geometry(&[circuit])?;
    if private.len() != circuit.raw.ninput - circuit.raw.npublic_input {
        return Err("prime frontend private input shape".into());
    }
    let (pads, suffix) =
        sumcheck_v2::sample_pads(&SumcheckProofGeometry::from_circuit(circuit), rng, f);
    let mut values = private;
    values.extend(suffix);
    Ok(Prepared {
        circuit_id: circuit.id,
        pads,
        values,
    })
}

pub(crate) fn prove<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    public: &[F::E],
    state: Prepared<W, F>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<(SumcheckProof<W, F>, LinearClaim<F::E>), String> {
    if state.circuit_id != circuit.id || public.len() != circuit.raw.npublic_input {
        return Err("prime frontend statement mismatch".into());
    }
    let private = circuit.raw.ninput - public.len();
    let mut inputs = public.to_vec();
    inputs.extend_from_slice(&state.values[..private]);
    transcript.write_sumcheck_statement(circuit, public, f);
    let (proof, constraints) =
        sumcheck_v2::evaluate_and_prove_circuits(&[circuit], inputs, &state.pads, transcript, f)?;
    let claim = row_batching::batch(circuit, public, constraints, transcript, f)?;
    Ok((proof, claim))
}
