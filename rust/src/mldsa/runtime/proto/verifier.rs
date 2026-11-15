// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{proto::Digest, zk::JointOpening};

impl<F1: SerializableField> JointOpening<(FieldProof<F1::E>, ())> for Proof<F1> {
    fn opening(&self) -> &JointPolygeroProof<(FieldProof<F1::E>, ())> {
        &self.polygero
    }
}

impl<F1: RuntimeField + SerializableField> Proof<F1> {
    pub(in crate::mldsa::runtime) fn read<'a>(
        bytes: &'a [u8],
        g: &Geometry,
        f1: &F1,
    ) -> Result<(&'a [u8], proof_transcript::Unverified<'a, Self>), String> {
        if bytes.get(..8)
            != Some(if g.simd_rounds.is_some() {
                b"MLDSA007"
            } else {
                b"MLDSA006"
            })
        {
            return Err("ML-DSA proof version or size".into());
        }
        let pg = v2_proto::polygero::PolygeroGeometry::new(g.binary.nw(), g.config)
            .map_err(|e| e.to_string())?;
        let width = f1.serialized_size_bytes();
        let [response, rows] =
            FieldProof::<()>::wire_lengths(&pg, width).ok_or("ML-DSA proof size overflow")?;
        let simd_bytes = g.simd_rounds.map(|r| (2 * r + 4) * width).unwrap_or(0);
        let fixed = [
            Some(32),
            Some(2 * width),
            Some(CLAIMS * MaskedWord::<{ super::super::QB }>::BYTES),
            g.binary.proof_len(width),
            Some(simd_bytes),
            Some(0),
            Some(response),
            Some(rows),
            JointPolygeroProof::<()>::fixed_opening_len(g.config.t),
        ]
        .into_iter()
        .try_fold(0usize, |n, x| n.checked_add(x?))
        .ok_or("ML-DSA proof size overflow")?;
        let mut remaining =
            v2_proto::polygero::codec::checked_body(bytes, 8, fixed, g.config.t, g.config.n)
                .map_err(|e| e.to_string())?;
        let commitment = PolygeroCommitment {
            root: Digest {
                data: v2_proto::read_bytes_32(&mut remaining).map_err(|e| e.to_string())?,
            },
        };
        use v2_proto::witness_selection::FingerprintResponse;
        let fingerprints =
            FingerprintResponse::read(&mut remaining, f1).map_err(|e| e.to_string())?;
        let mut masked = [MaskedWord::read(&mut remaining)?; CLAIMS];
        for m in &mut masked[1..] {
            *m = MaskedWord::read(&mut remaining)?;
        }
        let sumcheck_proof = SumcheckProof::read(&mut remaining, g.binary.sumcheck(), f1)
            .map_err(|e| e.to_string())?;
        let simd = if let Some(rounds) = g.simd_rounds {
            let nonlinear = v2_proto::read_field(&mut remaining, f1).map_err(|e| e.to_string())?;
            let dot = SumcheckProof::read(
                &mut remaining,
                &SumcheckProofGeometry::new(vec![rounds]).map_err(|e| e.to_string())?,
                f1,
            )
            .map_err(|e| e.to_string())?
            .layers
            .into_iter()
            .next()
            .ok_or("missing public SIMD proof")?;
            Some(PackedReduction { nonlinear, dot })
        } else {
            None
        };
        let packing = read_packing(g.binary.packing_degree(), &mut remaining, f1)?;
        let binary = CircuitProof {
            sumcheck_proof,
            packing,
        };
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            &mut remaining,
            g.config.t,
            g.config.n,
            |b| Ok((FieldProof::read_response(b, &pg, f1)?, ())),
            |b, rest| b.0.read_rows(rest, &pg, f1),
        )
        .map_err(|e| e.to_string())?;
        let body = Self {
            simd,
            masked,
            commitment,
            fingerprints,
            binary,
            polygero,
        };
        let mut seal = &bytes[bytes.len() - proof_transcript::SEAL_BYTES..];
        let decoded = proof_transcript::Unverified::decoded(body, bytes, &mut seal)
            .map_err(|e| e.to_string())?;
        Ok((seal, decoded))
    }
}
fn read_packing<F: SerializableField>(
    degree: usize,
    bytes: &mut &[u8],
    f: &F,
) -> Result<v2_proto::dual_packing::PackingProof<F::E>, String> {
    use v2_proto::dual_packing::PackingProof;
    if degree == 1 {
        return Ok(PackingProof::Direct);
    }
    let u = (0..degree)
        .map(|_| v2_proto::read_field(bytes, f).map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;
    let a = v2_proto::read_field(bytes, f).map_err(|e| e.to_string())?;
    Ok(PackingProof::TraceZero { u, a })
}
