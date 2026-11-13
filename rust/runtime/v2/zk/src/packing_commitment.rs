// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The packing/Polygero boundary. The commitment contains packed input words,
//! full-field sumcheck pads and terminal cells, then the packing masks. Packing
//! changes only the input claim; pad positions already refer to this physical
//! layout.
use crate::runtime::{
    algebra::{
        packing::{PackingExtension, PackingField, PackingParameters},
        ZkField,
    },
    v2::{
        dual_packing::generic::{FieldEquation, SourceClaim},
        polygero::PolygeroLinearTerm,
    },
};
/// Physical witness positions belong to ZK composition, rather than the
/// proof codec. Both roles derive them before the commitment is processed.
///
/// The cells are `[packed words | pads and terminal cells | packing masks]`:
/// frontend values in value order, then the packing reduction's masks. The
/// joint wrapper appends its fingerprint masks after all of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PackingLayout {
    pub(crate) private_inputs: usize,
    pub(crate) packed_words: usize,
    pub(crate) masks: usize,
    /// First pad cell: right after the packed words.
    pub(crate) suffix_start: usize,
    pub(crate) pad_cells: usize,
    /// First packing mask: right after the pads.
    pub(crate) masks_start: usize,
    pub(crate) witness_count: usize,
    pub(crate) degree: usize,
}
impl PackingLayout {
    pub(crate) fn new(
        private_inputs: usize,
        pad_cells: usize,
        degree: usize,
    ) -> Result<Self, String> {
        if degree == 0 {
            return Err("zero packing degree".into());
        }
        let packed_words = private_inputs.div_ceil(degree);
        let masks = if degree == 1 {
            0
        } else {
            degree.checked_add(1).ok_or("packing layout overflow")?
        };
        let suffix_start = packed_words;
        let masks_start = suffix_start
            .checked_add(pad_cells)
            .ok_or("packing layout overflow")?;
        let witness_count = masks_start
            .checked_add(masks)
            .ok_or("packing layout overflow")?;
        Ok(Self {
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            masks_start,
            witness_count,
            degree,
        })
    }
}
/// Backend handoff: one logical input claim and physical sumcheck linear rows.
#[must_use = "The source claim and linear rows require commitment authentication."]
pub(crate) struct CommitmentStatement<E> {
    pub(super) claim: SourceClaim<E>,
    pub(super) a: Vec<PolygeroLinearTerm<E>>,
    pub(super) b: Vec<E>,
}
pub(crate) struct PackingCommitment<
    F: PackingField,
    X: PackingExtension<Ambient = F> = <F as PackingField>::Packing,
> {
    pub(crate) parameters: PackingParameters<X>,
    pub(crate) layout: PackingLayout,
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub(crate) fn new(f: F, layout: PackingLayout, extension: X) -> Result<Self, String> {
        Ok(Self {
            parameters: PackingParameters::new(f, extension)?,
            layout,
        })
    }
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    /// Append the packing equations to the existing affine statement. The
    /// returned rows still require authentication by the joint backend.
    pub(super) fn append_equations<const W: usize>(
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
                    w: self.layout.masks_start + i,
                    k: k.clone(),
                });
            }
        }
        Ok((a, b))
    }
}
cfg_prover! { #[path="packing_commitment_prover.rs"]mod prover;pub(crate) use prover::PackingState; }
cfg_verifier! { #[path="packing_commitment_verifier.rs"]mod verifier; }
