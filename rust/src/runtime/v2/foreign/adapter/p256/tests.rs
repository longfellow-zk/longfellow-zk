// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The P-256 mode's statement values (transcript I3).
use super::{P256Mode, P256Plan};
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::gf2_128::Gf2_128Field,
        v2::{
            foreign::adapter::{fragment, transcript::write_layout, TreeShape},
            proto::tests::statement::Statement as Decoded,
            transcript::{Header, Opened, Statement, ZkStatement},
            zk::storage::{BitGroup, Group},
        },
    },
};

impl<const Q: usize> P256Mode<Q> {
    /// Check every value of this mode, as the verifier reads it, against
    /// the composed statement `d` decoded from the transcript: its
    /// `AdapterLayout`, the split participant's layout (the claim's terms are
    /// its foreign values and R) and the fragment's `Circuit` (the second
    /// circuit, regenerated here from the decoded values alone).
    pub(crate) fn check_absorbed_for_test(&self, d: &Decoded) {
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

impl<const Q: usize> P256Mode<Q> {
    /// Every field, in declaration order, with the plan's fields in place of
    /// the plan: the claim's term widths, their bit count, the pads, the
    /// tree shape, the virtual input count and the fragment. The patterns
    /// are exhaustive, so a new field does not compile until the statement
    /// tests cover it.
    pub(crate) fn fields_for_test(
        &self,
    ) -> (
        (&[usize], usize),
        &[BitGroup<Q>; 2],
        TreeShape,
        usize,
        &Circuit<Gf2_128Field>,
    ) {
        let P256Mode {
            plan,
            otp,
            shape,
            virtual_inputs,
            fragment,
        } = self;
        let P256Plan { widths, bits } = plan;
        ((widths, *bits), otp, *shape, *virtual_inputs, fragment)
    }
}

/// A statement that is a test identity and the messages `write` sends.
struct Only<W: Fn(&mut Header<'_>)>(W);
const IDENTITY: ZkStatement<'static> = ZkStatement {
    context: b"p256/adapter-layout",
};
impl<W: Fn(&mut Header<'_>)> Statement for Only<W> {
    type Identity = ZkStatement<'static>;
    fn identity(&self) -> &ZkStatement<'static> {
        &IDENTITY
    }
    fn write(&self, h: &mut Header<'_>) {
        (self.0)(h)
    }
}

/// The `AdapterLayout` encoder writes each of its values: the quotient
/// width Q, both fields of the tree shape, and each pad's start and width.
/// Each is changed alone here, below what a mode can construct: the tree
/// count is the mode's constant and the pads are Q bits wide.
#[test]
fn adapter_layout_writes_every_value() {
    fn bytes<const Q: usize>(shape: TreeShape, pads: [[usize; 2]; 2]) -> Vec<u8> {
        let groups = pads.map(|[start, width]| Group::new(start, width).unwrap());
        Opened::new(&Only(|h: &mut Header<'_>| {
            write_layout::<Q>(h, shape, groups)
        }))
        .statement_bytes_for_test()
        .to_vec()
    }
    let shape = TreeShape {
        trees: 2,
        leaves: 273,
    };
    let TreeShape { trees, leaves } = shape;
    let pads = [[100, 9], [109, 9]];
    let base = bytes::<9>(shape, pads);
    assert_ne!(bytes::<10>(shape, pads), base, "Q");
    let more_trees = TreeShape {
        trees: trees + 1,
        ..shape
    };
    assert_ne!(bytes::<9>(more_trees, pads), base, "trees");
    let more_leaves = TreeShape {
        leaves: leaves + 1,
        ..shape
    };
    assert_ne!(bytes::<9>(more_leaves, pads), base, "leaves");
    for pad in 0..2 {
        for value in 0..2 {
            let mut other = pads;
            other[pad][value] += 1;
            assert_ne!(bytes::<9>(shape, other), base, "pad {pad} value {value}");
        }
    }
}
