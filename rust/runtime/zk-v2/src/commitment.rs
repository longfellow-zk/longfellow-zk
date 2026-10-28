// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The sole packing/Polygero boundary. Full-field suffix positions are already physical.
use crate::runtime::{
    algebra::{
        packing::{PackingExtension, PackingField, PackingParameters},
        ZkField,
    },
    dual_packing::generic::{NativeEquation, SourceClaim},
    polygero::PolygeroLinearTerm,
    proto::zk_v2::PackingLayout,
    random::Transcript,
};
/// Backend handoff: one logical input claim and physical GKR linear rows.
pub(super) struct CommitmentStatement<E> {
    pub claim: SourceClaim<E>,
    pub a: Vec<PolygeroLinearTerm<E>>,
    pub b: Vec<E>,
}
pub(super) struct PackingCommitment<
    F: PackingField,
    X: PackingExtension<Ambient = F> = <F as PackingField>::Packing,
> {
    pub parameters: PackingParameters<X>,
    pub layout: PackingLayout,
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub fn new(f: F, layout: PackingLayout, extension: X) -> Result<Self, String> {
        Ok(Self {
            parameters: PackingParameters::new(f, extension)?,
            layout,
        })
    }
    pub fn bind(&self, t: &mut Transcript, id: &[u8; 32])
    where F: crate::core::algebra::SerializableField {
        t.write_bytes(b"longfellow/v2/packing-commitment/v1");
        t.write_bytes(id);
        t.write_bytes(&self.parameters.descriptor());
        for n in [self.layout.private_inputs, self.layout.pad_cells] {
            t.write_bytes(&(n as u64).to_le_bytes());
        }
    }
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub fn authenticate<const W: usize>(
        &self,
        statement: CommitmentStatement<F::E>,
        rows: &[NativeEquation<F::E>],
    ) -> Result<(Vec<PolygeroLinearTerm<F::E>>, Vec<F::E>), String>
    where
        F: ZkField<W>,
    {
        let expected = if self.layout.degree == 1 { 1 } else { 2 };
        if rows.len() != expected
            || rows.iter().any(|row| {
                row.masks.len() != self.layout.masks
                    || (!row.words.is_empty() && row.words.len() != self.layout.packed_words)
                    || row
                        .auxiliary
                        .iter()
                        .any(|(i, _)| *i >= self.layout.pad_cells)
            })
        {
            return Err("packing native equation shape".into());
        }
        let CommitmentStatement {
            claim,
            mut a,
            mut b,
        } = statement;
        drop(claim);
        for row in rows {
            let index = b.len();
            b.push(row.constant.clone());
            for (w, k) in row.words.iter().enumerate() {
                a.push(PolygeroLinearTerm {
                    c: index,
                    w,
                    k: k.clone(),
                });
            }
            for (i, k) in &row.auxiliary {
                a.push(PolygeroLinearTerm {
                    c: index,
                    w: self.layout.suffix_start + i,
                    k: k.clone(),
                });
            }
            for (i, k) in row.masks.iter().enumerate() {
                a.push(PolygeroLinearTerm {
                    c: index,
                    w: self.layout.packed_words + i,
                    k: k.clone(),
                });
            }
        }
        Ok((a, b))
    }
}
cfg_prover! { #[path="commitment_prover.rs"]mod prover;pub(super) use prover::CommitmentState; }
cfg_verifier! { #[path="commitment_verifier.rs"]mod verifier;pub(super) use verifier::CommitmentVerifier; }
