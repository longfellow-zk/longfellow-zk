// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The packing/Polygero boundary. The commitment contains packed input words,
//! packing masks, then full-field sumcheck pads and terminal cells. Packing changes
//! only the input claim; pad positions already refer to this physical layout.
use crate::runtime::{
    algebra::{
        packing::{PackingExtension, PackingField, PackingParameters},
        ZkField,
    },
    v2::{
        dual_packing::generic::{FieldEquation, SourceClaim},
        polygero::PolygeroLinearTerm,
        proto::zk::PackingLayout,
    },
};
/// Backend handoff: one logical input claim and physical sumcheck linear rows.
pub(crate) struct CommitmentStatement<E> {
    pub claim: SourceClaim<E>,
    pub a: Vec<PolygeroLinearTerm<E>>,
    pub b: Vec<E>,
}
pub(crate) struct PackingCommitment<
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
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub fn authenticate<const W: usize>(
        &self,
        statement: CommitmentStatement<F::E>,
        rows: &[FieldEquation<F::E>],
    ) -> Result<(Vec<PolygeroLinearTerm<F::E>>, Vec<F::E>), String>
    where
        F: ZkField<W>,
    {
        // Neither packing equation is sufficient by itself. Both enter the
        // same Polygero statement that authenticates the layer constraints.
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
            return Err("packing field equation shape".into());
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
cfg_prover! { #[path="packing_commitment_prover.rs"]mod prover;pub(crate) use prover::PackingState; }
cfg_verifier! { #[path="packing_commitment_verifier.rs"]mod verifier; }
