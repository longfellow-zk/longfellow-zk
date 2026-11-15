// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The P-256 mode's statement values (transcript I3).
use super::{P256Mode, P256Plan};
use crate::runtime::v2::{
    foreign::adapter::{fragment, TreeShape},
    proto::tests::statement::Statement,
};

impl<const Q: usize> P256Mode<Q> {
    /// Check every value of this mode, as the verifier reads it, against
    /// the composed statement `d` decoded from the transcript: its
    /// `AdapterLayout`, the split participant's layout (the claim's terms are
    /// its foreign values and R) and the fragment's `Circuit` (the second
    /// circuit, regenerated here from the decoded values alone).
    pub(crate) fn check_absorbed_for_test(&self, d: &Statement) {
        let P256Mode {
            plan,
            otp,
            shape,
            virtual_inputs,
            fragment: circuit,
        } = self;
        let P256Plan { widths, bits } = plan;
        let TreeShape { trees, leaves } = *shape;
        let [a] = &d.adapters[..] else {
            panic!("one adapter layout")
        };
        assert_eq!(
            a.mode,
            b"longfellow/v2/foreign/p256/two-full-field-trees/v1"
        );
        assert_eq!(a.q, Q as u64, "quotient bits");
        assert_eq!([a.trees, a.leaves], [trees, leaves].map(|x| x as u64));
        let pads: Vec<[u64; 2]> = otp
            .iter()
            .map(|g| [g.group().start(), g.group().width()].map(|x| x as u64))
            .collect();
        assert_eq!(a.pads, pads, "quotient pads");
        // The claim's terms, in term order: each foreign value of the split
        // participant (its stored runs, in value order), then R.
        let split = &d.layouts[1];
        let mut terms: Vec<usize> = split
            .stored
            .iter()
            .flat_map(|&[_, count, _, width]| std::iter::repeat_n(width as usize, count as usize))
            .collect();
        terms.push(split.mask[1] as usize);
        assert_eq!(*widths, terms, "claim term widths");
        let rebuilt = P256Plan::<Q>::new(terms).unwrap();
        assert_eq!(rebuilt, *plan);
        assert_eq!(*bits, widths.iter().sum::<usize>());
        assert_eq!(rebuilt.shape(), *shape, "tree shape");
        assert_eq!(*virtual_inputs, trees * leaves);
        // R, then both pads, follow each other in the reserved suffix; the
        // virtual leaves start after the last pad.
        assert_eq!(a.pads[0][0], split.mask[0] + split.mask[1]);
        assert_eq!(a.pads[1][0], a.pads[0][0] + a.pads[0][1]);
        let start = (a.pads[1][0] + a.pads[1][1]) as usize;
        let npublic = d.public[0].elements.len();
        let regenerated = fragment(npublic, start, rebuilt.shape()).unwrap();
        assert_eq!(regenerated.id, d.circuits[1], "the fragment's ID");
        assert_eq!(circuit.id, d.circuits[1]);
    }
}
