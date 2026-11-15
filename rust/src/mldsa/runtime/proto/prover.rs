// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::proto::sumcheck::LayerProof;
impl<F1: RuntimeField + SerializableField> Proof<F1> {
    pub(in crate::mldsa::runtime) fn write(
        &self,
        g: &Geometry,
        f1: &F1,
        transcript: proof_transcript::Transcript,
    ) -> Result<proof_transcript::EncodedProof, String> {
        let pg = v2_proto::polygero::PolygeroGeometry::new(g.binary.nw(), g.config)
            .map_err(|e| e.to_string())?;
        let mut out = Vec::new();
        out.extend_from_slice(if g.simd_rounds.is_some() {
            b"MLDSA007"
        } else {
            b"MLDSA006"
        });
        out.extend_from_slice(&self.commitment.root.data);
        self.fingerprints.write(&mut out, f1);
        for m in &self.masked {
            m.write(&mut out);
        }
        self.binary
            .sumcheck_proof
            .write_to_buf(&mut out, g.binary.sumcheck(), f1)
            .map_err(|e| e.to_string())?;
        match (g.simd_rounds, &self.simd) {
            (Some(rounds), Some(proof)) => {
                out.extend(f1.to_bytes(&proof.nonlinear));
                SumcheckProof {
                    layers: vec![LayerProof {
                        rounds: proof.dot.rounds.clone(),
                        cross: proof.dot.cross.clone(),
                        claims: proof.dot.claims.clone(),
                    }],
                }
                .write_to_buf(
                    &mut out,
                    &SumcheckProofGeometry::new(vec![rounds]).map_err(|e| e.to_string())?,
                    f1,
                )
                .map_err(|e| e.to_string())?;
            }
            (None, None) => {}
            _ => return Err("public SIMD codec geometry".into()),
        }
        write_packing(
            &self.binary.packing,
            g.binary.packing_degree(),
            &mut out,
            f1,
        )?;
        self.polygero
            .write_to_buf::<std::io::Error>(
                &mut out,
                g.config.t,
                g.config.n,
                |b, buffer| b.0.write_response(buffer, &pg, f1),
                |b, buffer| b.0.write_rows(buffer, &pg, f1),
            )
            .map_err(|e| e.to_string())?;
        Ok(transcript.append_final_seal(out))
    }
}
fn write_packing<F: SerializableField>(
    proof: &v2_proto::dual_packing::PackingProof<F::E>,
    degree: usize,
    out: &mut Vec<u8>,
    f: &F,
) -> Result<(), String> {
    use v2_proto::dual_packing::PackingProof;
    match proof {
        PackingProof::Direct if degree == 1 => Ok(()),
        PackingProof::TraceZero { u, a } if degree > 1 && u.len() == degree => {
            for x in u.iter().chain(std::iter::once(a)) {
                out.extend(f.to_bytes(x));
            }
            Ok(())
        }
        _ => Err("ML-DSA packing geometry".into()),
    }
}
