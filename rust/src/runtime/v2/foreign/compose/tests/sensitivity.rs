// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One-field sensitivity of the composed statement (transcript I1, I3), on
//! the parent module's tiny composition: the composed geometry and the
//! P-256 mode. As in `zk::tests::sensitivity`, each test destructures its
//! type exhaustively, and a derived field changes through a written value it
//! derives from (the round-trip test rebuilds it from the decoded
//! statement).
use super::{super::Composition, circuit, CONFIG, LABEL, WIDTH};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        v2::{
            foreign::adapter::{p256::P256Mode, AdapterMode, TreeShape},
            proto::{composed::ComposedGeometry, polygero::PolygeroConfig},
            transcript::{Opened, ZkStatement},
            zk::{
                split::value_count,
                storage::{Group, StorageMap},
            },
        },
    },
};

/// The P-256 mode's values: the claim's term widths and their bit count,
/// the pads' starts (each Q bits wide), the tree shape, the virtual input count and the
/// fragment's ID.
#[derive(Debug, PartialEq, Eq)]
struct ModeValues {
    widths: Vec<usize>,
    bits: usize,
    pads: [usize; 2],
    shape: TreeShape,
    virtual_inputs: usize,
    fragment: [u8; 32],
}

/// A tiny composition whose host has `host_inputs` inputs and whose split
/// circuit has `split_inputs`, with the split values `foreign` stored as bit
/// groups, under `config`: its statement bytes, geometry and mode values.
fn composed<const Q: usize>(
    host_inputs: usize,
    split_inputs: usize,
    foreign: &[(usize, Group)],
    config: PolygeroConfig,
) -> (Vec<u8>, ComposedGeometry, ModeValues) {
    let gf2 = Gf2_128Field::new();
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let host_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let split_domain =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    let host = circuit(&gf2, host_inputs, vec![gf2.one()], &[(0, 0), (1, 0)]);
    let split = circuit(&p, split_inputs, vec![p.one(), p.mone()], &[(1, 0), (2, 1)]);
    let storage = StorageMap::new(value_count(&split).unwrap(), foreign).unwrap();
    let c = Composition::<4, P256Field, _, _, P256Mode<Q>>::new(
        &host,
        &split,
        storage,
        config,
        (&host_domain, &split_domain),
    )
    .unwrap();
    let split_public = [p.one()];
    let statement = c
        .statement(ZkStatement { context: LABEL }, &[true], &split_public)
        .unwrap();
    let bytes = Opened::new(&statement).statement_bytes_for_test().to_vec();
    let ((widths, bits), otp, shape, virtual_inputs, fragment) = c.mode().fields_for_test();
    let values = ModeValues {
        widths: widths.to_vec(),
        bits,
        pads: otp.map(|g| g.fields_for_test()),
        shape,
        virtual_inputs,
        fragment: fragment.id,
    };
    (bytes, statement.geometry().clone(), values)
}

fn shared(width: usize) -> [(usize, Group); 1] {
    [(0, Group::new(1, width).unwrap())]
}

#[test]
fn composed_geometry_fields_are_absorbed() {
    let (base, geometry, _) = composed::<9>(1 + WIDTH, 3, &shared(WIDTH), CONFIG);
    let (host, split, config) = geometry.fields_for_test();
    // The host's circuit geometry, derived from the host circuit and the
    // fragment, which the `Circuit` IDs hash: enough host inputs for one
    // more packed word of the committed inputs (format private inputs, R
    // and the pads).
    {
        let (bytes, other, _) = composed::<9>(1 + WIDTH + 103, 3, &shared(WIDTH), CONFIG);
        assert_ne!(other.fields_for_test().0, host);
        assert_ne!(bytes, base, "host geometry");
    }
    // The split circuit geometry, derived from the split circuit and its
    // storage: one more split input.
    {
        let (bytes, other, _) = composed::<9>(1 + WIDTH, 4, &shared(WIDTH), CONFIG);
        assert_ne!(other.fields_for_test().1, split);
        assert_ne!(bytes, base, "split geometry");
    }
    // The profile, written in `JointGeometry`: each value.
    assert_eq!(config, CONFIG);
    let PolygeroConfig { k, s, n, t } = config;
    for (name, changed) in [
        ("k", PolygeroConfig { k: k + 1, ..CONFIG }),
        ("s", PolygeroConfig { s: s + 1, ..CONFIG }),
        ("n", PolygeroConfig { n: n + 1, ..CONFIG }),
        ("t", PolygeroConfig { t: t + 1, ..CONFIG }),
    ] {
        let (bytes, other, _) = composed::<9>(1 + WIDTH, 3, &shared(WIDTH), changed);
        assert_eq!(other.fields_for_test().2, changed);
        assert_ne!(bytes, base, "profile {name}");
    }
}

#[test]
fn adapter_fields_are_absorbed() {
    let (base, _, mode) = composed::<9>(1 + WIDTH, 3, &shared(WIDTH), CONFIG);
    let ModeValues {
        widths,
        bits,
        pads,
        shape,
        virtual_inputs,
        fragment,
    } = &mode;
    let TreeShape { trees, leaves } = *shape;
    // Q, the mode's quotient width, written in `AdapterLayout`; it also
    // widens the pads and the trees.
    {
        let (bytes, _, other) = composed::<10>(1 + WIDTH, 3, &shared(WIDTH), CONFIG);
        assert_ne!(other.shape.leaves, leaves);
        assert_ne!(bytes, base, "Q");
    }
    // The claim's term widths, each element: the foreign value's width (in
    // the split layout's stored runs), alone. The last term is R, whose
    // width is the mode's constant `MASK_BITS`, so it cannot change.
    assert_eq!(
        *widths,
        [WIDTH, <P256Mode<9> as AdapterMode<P256Field>>::MASK_BITS]
    );
    {
        let (bytes, _, other) = composed::<9>(1 + WIDTH, 3, &shared(WIDTH - 1), CONFIG);
        assert_eq!(other.widths, [WIDTH - 1, widths[1]]);
        assert_ne!(bytes, base, "term width");
        // Derived from the widths: their bit count, the leaves per tree (bits +
        // Q, written), the virtual inputs (trees x leaves) and the fragment
        // (written as the second circuit's ID).
        assert_ne!(other.bits, *bits);
        assert_ne!(other.shape.leaves, leaves);
        assert_ne!(other.virtual_inputs, *virtual_inputs);
        assert_ne!(other.fragment, *fragment);
    }
    // The tree count is the mode's constant: two full-field trees, which
    // the mode ID names, so it cannot change here; the `AdapterLayout`
    // encoder writes it (`adapter_layout_writes_every_value`).
    assert_eq!(trees, 2);
    // The pads, written by start and width (Q bits): they follow R after the
    // host circuit's inputs, so one more host input moves both.
    {
        let (bytes, _, other) = composed::<9>(2 + WIDTH, 3, &shared(WIDTH), CONFIG);
        assert_eq!(other.pads, pads.map(|start| start + 1));
        assert_ne!(bytes, base, "pads");
    }
}
