// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment, PackingLayout};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field,
            packing::{binary::Binary128Extension, PackingExtension},
        },
        v2::dual_packing::generic::{Affine, FieldEquation, SourceClaim},
    },
};

impl PackingLayout {
    /// Every field, in declaration order: private inputs, packed words,
    /// masks, suffix start, pad cells, masks start, witness count, degree.
    /// The pattern is exhaustive, so a new field does not compile until the
    /// statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> [usize; 8] {
        let Self {
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            masks_start,
            witness_count,
            degree,
        } = *self;
        [
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            masks_start,
            witness_count,
            degree,
        ]
    }
}

/// `append_equations` takes exactly the packing rows of this layout: one row
/// per packing equation (two for a degree above one), each with one mask
/// coefficient per packing mask, no words or one per packed word, and
/// auxiliary cells among the pads. Any other row set is rejected before a
/// term is appended.
#[test]
fn append_equations_rejects_rows_of_another_shape() {
    let f = Gf2_128Field::new();
    let extension = Binary128Extension;
    assert!(extension.degree() > 1);
    let layout = PackingLayout::new(300, 3, extension.degree()).unwrap();
    let (words, masks, pads) = (layout.packed_words, layout.masks, layout.pad_cells);
    let backend = PackingCommitment::new(f.clone(), layout, extension).unwrap();
    let statement = || CommitmentStatement {
        claim: SourceClaim {
            weights: vec![],
            rhs: Affine {
                constant: f.zero(),
                terms: vec![],
            },
            auxiliary_count: 0,
        },
        a: vec![],
        b: vec![],
    };
    let row = |w: usize, m: usize, auxiliary: usize| FieldEquation {
        constant: f.one(),
        words: vec![f.one(); w],
        auxiliary: vec![(auxiliary, f.one())],
        masks: vec![f.one(); m],
    };
    let append = |rows: &[FieldEquation<_>]| backend.append_equations(statement(), rows);
    let (a, b) = append(&[row(words, masks, 0), row(0, masks, pads - 1)]).unwrap();
    assert_eq!((a.len(), b.len()), (words + 2 * masks + 2, 2));
    for rows in [
        vec![row(words, masks, 0)],
        vec![row(words, masks, 0); 3],
        vec![row(words, masks - 1, 0), row(0, masks, 0)],
        vec![row(words - 1, masks, 0), row(0, masks, 0)],
        vec![row(words, masks, 0), row(0, masks, pads)],
    ] {
        assert_eq!(append(&rows).err().unwrap(), "packing field equation shape");
    }
}

/// The layout counts packed words and masks for its packing degree, and the
/// parameters pack words and sample masks for the extension's. A layout of
/// another degree would describe cells the commitment does not produce
/// (`PackingLayout::new(128, 0, 1)` with the degree-128 binary extension
/// declares 128 cells, the packing produces 130), so construction rejects
/// it.
#[test]
fn packing_commitment_rejects_a_layout_of_another_degree() {
    let f = Gf2_128Field::new();
    let extension = Binary128Extension;
    assert_eq!(extension.degree(), 128);
    let narrow = PackingLayout::new(128, 0, 1).unwrap();
    assert_eq!(
        PackingCommitment::new(f.clone(), narrow, extension)
            .err()
            .unwrap(),
        "packing layout degree differs from the extension degree"
    );
    let matching = PackingLayout::new(128, 0, extension.degree()).unwrap();
    assert!(PackingCommitment::new(f, matching, extension).is_ok());
}

#[test]
fn simd_source_preserves_private_inputs_and_rejects_aliasing_layouts() {
    let layout = PackingLayout::for_simd_source(129, 3, 7).unwrap();
    assert_eq!(layout.private_inputs, 129);
    assert_eq!(layout.packed_words, 3);
    assert_eq!(layout.suffix_start, 3);
    assert_eq!(layout.masks_start, 10);
    assert_eq!(layout.witness_count, 10);
    assert_eq!(layout.degree, 1);
    assert_eq!(layout.masks, 0);
    assert!(PackingLayout::for_simd_source(129, 1, 7).is_err());
    assert!(PackingLayout::for_simd_source(0, usize::MAX, 1).is_err());
    assert!(PackingLayout::for_simd_source(1, 1, usize::MAX).is_err());
}
