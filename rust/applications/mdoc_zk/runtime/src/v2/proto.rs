// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Two circuit reductions with one shared Polygero commitment and opening.
use crate::{
    core::proto::SerializableField,
    runtime::{
        algebra::RuntimeField,
        proto::{
            polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
            zk_v2::{CircuitProof, ZkProofGeometry},
            Digest,
        },
    },
};
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProofGeometry {
    pub geom_hash: ZkProofGeometry,
    pub geom_sig: ZkProofGeometry,
    pub joint_context: Digest,
    pub config: PolygeroConfig,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProof<F1: SerializableField, F2: SerializableField> {
    pub macs: [u128; 6],
    pub commitment: PolygeroCommitment,
    pub proof_hash: CircuitProof<2, F1>,
    pub proof_sig: CircuitProof<4, F2>,
    pub polygero: JointPolygeroProof<(FieldProof<F1::E>, (FieldProof<F2::E>, ()))>,
}
impl<F1: RuntimeField<2> + SerializableField, F2: RuntimeField<4> + SerializableField>
    MdocProof<F1, F2>
{
    pub fn write(&self, g: &MdocProofGeometry, f1: &F1, f2: &F2) -> Result<Vec<u8>, String> {
        let mut out = Vec::new();
        for m in &self.macs {
            out.extend_from_slice(&m.to_le_bytes());
        }
        out.extend_from_slice(b"MJP2");
        out.extend_from_slice(&self.commitment.root.data);
        self.proof_hash
            .write_to_buf(&mut out, &g.geom_hash, f1)
            .map_err(|e| e.to_string())?;
        self.proof_sig
            .write_to_buf(&mut out, &g.geom_sig, f2)
            .map_err(|e| e.to_string())?;
        self.polygero
            .write_to_buf::<std::io::Error>(
                &mut out,
                &g.joint_context,
                g.config.t,
                g.config.n,
                |b, out| {
                    b.0.write(out, &g.geom_hash.com_geom, f1)?;
                    b.1 .0.write(out, &g.geom_sig.com_geom, f2)
                },
            )
            .map_err(|e| e.to_string())?;
        Ok(out)
    }
    pub fn read<'a>(
        bytes: &'a [u8],
        g: &MdocProofGeometry,
        f1: &F1,
        f2: &F2,
    ) -> Result<(&'a [u8], Self), String> {
        if bytes.len() < 100 || bytes.get(96..100) != Some(b"MJP2") {
            return Err("mdoc joint proof version or size".into());
        }
        let mut remaining = bytes;
        let mut macs = [0u128; 6];
        for m in &mut macs {
            *m = u128::from_le_bytes(remaining[..16].try_into().unwrap());
            remaining = &remaining[16..];
        }
        remaining = &remaining[4..];
        let commitment = PolygeroCommitment {
            root: Digest {
                data: crate::runtime::proto::util::read_bytes_32(&mut remaining)
                    .map_err(|e| e.to_string())?,
            },
        };
        let proof_hash =
            CircuitProof::read(&mut remaining, &g.geom_hash, f1).map_err(|e| e.to_string())?;
        let proof_sig =
            CircuitProof::read(&mut remaining, &g.geom_sig, f2).map_err(|e| e.to_string())?;
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            &mut remaining,
            &g.joint_context,
            g.config.t,
            g.config.n,
            |b| {
                Ok((
                    FieldProof::read(b, &g.geom_hash.com_geom, f1)?,
                    (FieldProof::read(b, &g.geom_sig.com_geom, f2)?, ()),
                ))
            },
        )
        .map_err(|e| e.to_string())?;
        Ok((
            remaining,
            Self {
                macs,
                commitment,
                proof_hash,
                proof_sig,
                polygero,
            },
        ))
    }
}
