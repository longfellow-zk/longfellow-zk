// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The packing/Polygero boundary. The commitment contains packed input words,
//! full-field sumcheck pads and terminal cells, then the packing masks. Packing
//! changes only the input claim; pad positions already refer to this physical
//! layout.
use crate::runtime::{
    algebra::{
        packing::{AmbientElement, PackingExtension, PackingParameters},
        ZkField,
    },
    v2::{
        dual_packing::generic::{mask_cell_count, FieldEquation, SourceClaim},
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
    packed_words: usize,
    masks: usize,
    /// First pad cell: right after the packed words.
    pub(crate) suffix_start: usize,
    pub(crate) pad_cells: usize,
    /// First packing mask: right after the pads.
    masks_start: usize,
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
        let masks = mask_cell_count(degree).ok_or("packing layout overflow")?;
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
/// The packing commitment of the extension `X`, whose ambient field
/// (`X::Ambient`) is the commitment's field.
pub(crate) struct PackingCommitment<X: PackingExtension> {
    pub(crate) parameters: PackingParameters<X>,
    pub(crate) layout: PackingLayout,
}
impl<X: PackingExtension> PackingCommitment<X> {
    pub(crate) fn new(f: X::Ambient, layout: PackingLayout, extension: X) -> Result<Self, String> {
        // The layout counts packed words and masks for its own degree; the
        // parameters pack and sample masks for the extension's.
        if layout.degree != extension.degree() {
            return Err("packing layout degree differs from the extension degree".into());
        }
        Ok(Self {
            parameters: PackingParameters::new(f, extension)?,
            layout,
        })
    }
}
impl<X: PackingExtension> PackingCommitment<X> {
    /// Append the packing equations to the existing affine statement. The
    /// returned rows still require authentication by the joint backend.
    pub(super) fn append_equations(
        &self,
        statement: CommitmentStatement<AmbientElement<X>>,
        rows: &[FieldEquation<AmbientElement<X>>],
    ) -> Result<
        (
            Vec<PolygeroLinearTerm<AmbientElement<X>>>,
            Vec<AmbientElement<X>>,
        ),
        String,
    >
    where
        X::Ambient: ZkField,
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
cfg_prover! { pub(crate) mod prover; }
cfg_verifier! { mod verifier; }

#[cfg(feature = "mldsa")]
impl<E> CommitmentStatement<E> {
    /// Transfer the source claim and layer rows to a composed host. Auxiliary
    /// positions become host witness positions starting at `base`.
    pub(crate) fn into_parts(
        self,
        base: usize,
    ) -> (
        Vec<E>,
        E,
        Vec<(usize, E)>,
        Vec<PolygeroLinearTerm<E>>,
        Vec<E>,
    ) {
        (
            self.claim.weights,
            self.claim.rhs.constant,
            self.claim
                .rhs
                .terms
                .into_iter()
                .map(|(i, k)| {
                    (
                        base.checked_add(i)
                            .expect("auxiliary witness position overflow"),
                        k,
                    )
                })
                .collect(),
            self.a,
            self.b,
        )
    }
}

#[cfg(any(test, feature = "mldsa"))]
impl PackingLayout {
    /// An already packed SIMD source, including its own authenticated masks,
    /// followed by scalar sumcheck pads. No additional packing reduction applies.
    pub(crate) fn for_simd_source(
        private_inputs: usize,
        source_words: usize,
        pad_cells: usize,
    ) -> Result<Self, String> {
        if source_words < private_inputs.div_ceil(128) {
            return Err("SIMD source does not cover the private Boolean inputs".into());
        }
        let witness_count = source_words
            .checked_add(pad_cells)
            .ok_or("SIMD packing layout overflow")?;
        Ok(Self {
            private_inputs,
            packed_words: source_words,
            masks: 0,
            suffix_start: source_words,
            pad_cells,
            masks_start: witness_count,
            witness_count,
            degree: 1,
        })
    }
}

#[cfg(test)]
mod tests;
