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
    pub mu: F2::E,
    pub masked: Vec<u8>,
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
        let plan = crate::mdoc::circuits::p256_adapter::shared_plan();
        plan.validate_advice(&self.masked)?;
        out.extend_from_slice(b"MDA4");
        out.extend_from_slice(&self.commitment.root.data);
        out.extend_from_slice(&f2.to_bytes(&self.mu));
        out.extend_from_slice(&self.masked);
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
        if bytes.get(..4) != Some(b"MDA4") {
            return Err("mdoc adapter proof version or size".into());
        }
        let mut remaining = &bytes[4..];
        let commitment = PolygeroCommitment {
            root: Digest {
                data: crate::runtime::proto::util::read_bytes_32(&mut remaining)
                    .map_err(|e| e.to_string())?,
            },
        };
        let size = f2.serialized_size_bytes();
        let plan = crate::mdoc::circuits::p256_adapter::shared_plan();
        if remaining.len() < size + plan.advice_bytes() {
            return Err("truncated adapter proof".into());
        }
        let mu = f2
            .bytes_to_element(&remaining[..size])
            .map_err(|e| e.to_string())?;
        if f2.to_bytes(&mu) != remaining[..size] {
            return Err("noncanonical adapter scalar".into());
        }
        remaining = &remaining[size..];
        let masked = remaining[..plan.advice_bytes()].to_vec();
        plan.validate_advice(&masked)?;
        remaining = &remaining[plan.advice_bytes()..];
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
                mu,
                masked,
                commitment,
                proof_hash,
                proof_sig,
                polygero,
            },
        ))
    }
}
