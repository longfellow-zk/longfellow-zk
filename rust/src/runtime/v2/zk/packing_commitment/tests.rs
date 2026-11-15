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
    let append = |rows: &[FieldEquation<_>]| backend.append_equations::<2>(statement(), rows);
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
