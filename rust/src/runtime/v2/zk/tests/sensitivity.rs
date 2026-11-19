// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One-field sensitivity of the statement (transcript I1, I3).
//!
//! Each test destructures a real value of an instance type the statement is
//! built from with an exhaustive pattern, directly or through the type's
//! `fields_for_test` (exhaustive, next to the type), so a new field does not
//! compile until it is covered here. For each field it builds the statement
//! with that value changed and checks that the statement bytes change.
//!
//! A field the statement writes is changed alone, in the participant the
//! statement is written from. A field the verifier derives from written
//! values (the round-trip tests in `absorption` rebuild each one from the
//! decoded statement) cannot change alone; it is changed through a written
//! value it derives from, the comment at each says which, and the test
//! checks that the field did change.
use std::collections::BTreeSet;

use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::v2::{Circuit, Layer, Linear, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            packing::{
                binary::{Binary128Extension, Binary128Over256},
                PackingExtension, PackingField, PackingParameters,
            },
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        v2::{
            proto::{polygero::PolygeroConfig, zk::ZkProofGeometry},
            transcript::{Header, Opened, Statement, ZkStatement},
            zk::{
                joint::{CircuitParticipant, FrontendPart},
                split::{value_count, MixedSplit},
                storage::{Group, MixedStorage, Run, Storage, StorageMap},
                write_joint_geometry, ZkProofStatement, ZkVerifier,
            },
        },
    },
};

const CONTEXT: &[u8] = b"longfellow/v2/test/sensitivity";
const CONFIG: PolygeroConfig = PolygeroConfig {
    k: 8,
    s: 2,
    n: 64,
    t: 2,
};

/// The bytes a session opened with `s` hashes before any proof byte.
fn statement_bytes<S: Statement>(s: &S) -> Vec<u8> {
    Opened::new(s).statement_bytes_for_test().to_vec()
}

/// A circuit of `f` with `ninput` inputs, the first public, and layers of
/// input widths `widths` (outputs to inputs) above its input layer. Each
/// output copies one input of its layer; the one top output is asserted
/// zero.
fn layered<F: SerializableField + AlgebraicField>(
    f: &F,
    ninput: usize,
    widths: &[usize],
) -> Circuit<F> {
    let mut nw = widths.to_vec();
    nw.push(ninput);
    let layers = (0..nw.len())
        .map(|i| {
            let outputs = if i == 0 { 1 } else { nw[i - 1] };
            let terms = (0..outputs).map(|g| Linear {
                g: g as u32,
                l: (g % nw[i]) as u32,
                k: 0,
            });
            Layer::new(
                nw[i],
                Stream::default(),
                Stream::<Linear>::from_terms(terms),
                Stream::default(),
            )
        })
        .collect();
    let raw = RawCircuitBuilder {
        ninput,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.one()],
        layers,
    }
    .build();
    Circuit::from_raw(f, raw)
}

/// The statement of a standalone GF(2^128) verifier of `circuit` under
/// `config`, its geometry and its commitment layout's fields.
fn standalone(
    circuit: Circuit<Gf2_128Field>,
    config: PolygeroConfig,
) -> (Vec<u8>, ZkProofGeometry, [usize; 8]) {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let verifier = ZkVerifier::new(circuit, config, &d).unwrap();
    let statement = verifier.statement(CONTEXT, &[true]).unwrap();
    let cells = statement
        .part
        .participant
        .frontend
        .backend
        .layout
        .fields_for_test();
    (statement_bytes(&statement), verifier.geometry(), cells)
}

/// The same statement, written from a participant that `edit` changed
/// after construction: the values the `CommitmentLayout` encoder reads.
fn edited(
    circuit: &Circuit<Gf2_128Field>,
    edit: impl FnOnce(&mut CircuitParticipant<Gf2_128Field>),
) -> Vec<u8> {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let mut participant = CircuitParticipant::new(&[circuit], 0, CONFIG, &d).unwrap();
    let geometry = ZkProofGeometry::new(participant.geometry(), CONFIG).unwrap();
    edit(&mut participant);
    statement_bytes(&ZkProofStatement {
        identity: ZkStatement { context: CONTEXT },
        part: FrontendPart::new(&participant, &[circuit], &[true]).unwrap(),
        geometry,
    })
}

#[test]
fn polygero_profile_fields_are_absorbed() {
    let f = Gf2_128Field::new();
    let (base, ..) = standalone(layered(&f, 9, &[4, 8]), CONFIG);
    let PolygeroConfig { k, s, n, t } = CONFIG;
    for (name, config) in [
        ("k", PolygeroConfig { k: k + 1, ..CONFIG }),
        ("s", PolygeroConfig { s: s + 1, ..CONFIG }),
        ("n", PolygeroConfig { n: n + 1, ..CONFIG }),
        ("t", PolygeroConfig { t: t + 1, ..CONFIG }),
    ] {
        let (other, geometry, _) = standalone(layered(&f, 9, &[4, 8]), config);
        assert_eq!(geometry.fields_for_test().1, config);
        assert_ne!(other, base, "profile {name}");
    }
}

#[test]
fn proof_geometry_fields_are_absorbed() {
    let f = Gf2_128Field::new();
    let circuit = || layered(&f, 9, &[4, 8]);
    let (base, geometry, cells) = standalone(circuit(), CONFIG);
    // The edited participant writes the verifier's statement.
    assert_eq!(edited(&circuit(), |_| {}), base);
    let geometry_of = |ninput, widths: &[usize]| {
        let (bytes, g, layout) = standalone(layered(&f, ninput, widths), CONFIG);
        assert_ne!(bytes, base, "{ninput} inputs, layer widths {widths:?}");
        (g, layout)
    };
    // ZkProofGeometry: the circuit geometry, below, and the profile
    // (`polygero_profile_fields_are_absorbed`).
    let (circuit_geometry, config) = geometry.fields_for_test();
    assert_eq!(config, CONFIG);
    // CircuitProofGeometry.
    let (sumcheck, packing_degree, nw) = circuit_geometry.fields_for_test();
    // SumcheckProofGeometry: each layer's round count, from its width in
    // the circuit the `Circuit` ID hashes, one layer at a time; then the
    // layer count. The input layer's width is the input count, which also
    // changes the committed inputs.
    let logw = sumcheck.fields_for_test();
    assert_eq!(logw, [2, 3, 4]);
    for (layer, ninput, widths) in [(0, 9, &[8, 8][..]), (1, 9, &[4, 16]), (2, 17, &[4, 8])] {
        let (g, _) = geometry_of(ninput, widths);
        let other = g.fields_for_test().0.fields_for_test().0.fields_for_test();
        let changed: Vec<usize> = (0..logw.len()).filter(|&i| other[i] != logw[i]).collect();
        assert_eq!(changed, [layer]);
    }
    {
        let (g, _) = geometry_of(9, &[4, 8, 8]);
        assert_eq!(
            g.fields_for_test()
                .0
                .fields_for_test()
                .0
                .fields_for_test()
                .len(),
            4
        );
    }
    // The packing degree: a GF(2^128) participant packs bits at degree 128
    // (the authenticated bit-input profile, the only one it accepts) and a
    // P-256 participant has degree one, so it cannot change within a field.
    // The descriptor carries it: `packing_descriptor_fields_are_absorbed`.
    assert_eq!(packing_degree, 128);
    // The committed cell count: derived from the private input and pad
    // counts and the degree; one more packed word of private inputs.
    {
        let (g, _) = geometry_of(1 + 129, &[4, 8]);
        assert_ne!(g.fields_for_test().0.fields_for_test().2, nw);
    }

    // PackingLayout.
    let [private_inputs, packed_words, masks, suffix_start, pad_cells, masks_start, witness_count, degree] =
        cells;
    // Written: the private input count, alone and through the circuit.
    assert_ne!(
        edited(&circuit(), |p| p.frontend.backend.layout.private_inputs +=
            1),
        base
    );
    {
        let (_, other) = geometry_of(10, &[4, 8]);
        assert_ne!(other[0], private_inputs);
    }
    // Derived from the private inputs and the degree: the packed words and
    // the suffix start (the first pad cell follows the packed words).
    {
        let (_, other) = geometry_of(1 + 129, &[4, 8]);
        assert_ne!([other[1], other[3]], [packed_words, suffix_start]);
    }
    // Derived from the degree alone: the packing masks (degree + 1, none at
    // degree one), and the degree itself, fixed by the field as above.
    assert_eq!((masks, degree), (129, 128));
    // Written: the pad count, alone and through the circuit's layers.
    assert_ne!(
        edited(&circuit(), |p| p.frontend.backend.layout.pad_cells += 1),
        base
    );
    let (_, other) = geometry_of(9, &[8, 8]);
    assert_ne!(other[4], pad_cells);
    // Derived from the packed words and the pads: the first mask and the
    // witness count.
    assert_ne!([other[5], other[6]], [masks_start, witness_count]);
}

#[test]
fn packing_descriptor_fields_are_absorbed() {
    let f = Gf2_128Field::new();
    let circuit = layered(&f, 9, &[4, 8]);
    let base = edited(&circuit, |_| {});
    let parameters = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    let (field, extension, basis, dual, inverse) = parameters.fields_for_test();
    // The field: its packing ID opens the descriptor (and its FieldID opens
    // the layout); a P-256 descriptor differs.
    assert_eq!(field.field_id(), f.field_id());
    let p = P256Field::new();
    let prime = PackingParameters::new(p.clone(), p.packing_extension()).unwrap();
    assert_ne!(prime.descriptor(), parameters.descriptor());
    // The extension: its embedding ID and degree. GF(2^128) participants
    // accept only `Binary128Extension`, so another extension of the same
    // field (here over GF(256), degree 16) cannot be written by a
    // participant; its descriptor differs.
    assert_eq!(extension.degree(), 128);
    let over256 = PackingParameters::new(f.clone(), Binary128Over256::new()).unwrap();
    assert_ne!(over256.descriptor(), parameters.descriptor());
    // The basis, each element written: a spread sample of elements, each
    // changed alone (adding the first element, one, keeps a basis). The
    // first must be one.
    for j in [1, 2, 64, 127] {
        let mut changed = basis.to_vec();
        f.add(&mut changed[j], &f.one());
        let other = PackingParameters::with_basis(f.clone(), Binary128Extension, changed).unwrap();
        // Derived from the basis and the extension: the trace-dual basis
        // and, for a basis other than the native one, the coordinate inverse.
        assert!(other.fields_for_test().4.is_some());
        let bytes = edited(&circuit, |participant| {
            participant.frontend.backend.parameters = other
        });
        assert_ne!(bytes, base, "basis element {j}");
    }
    assert_eq!(dual.len(), 128);
    assert!(inverse.is_none(), "the native basis needs no inverse");
}

/// A P-256 circuit whose one output, asserted zero, sums its `ninput`
/// inputs, the first public.
fn prime_circuit(p: &P256Field, ninput: usize) -> Circuit<P256Field> {
    let terms = (0..ninput).map(|l| Linear {
        g: 0,
        l: l as u32,
        k: 0,
    });
    let raw = RawCircuitBuilder {
        ninput,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![p.one()],
        layers: vec![Layer::new(
            ninput,
            Stream::default(),
            Stream::<Linear>::from_terms(terms),
            Stream::default(),
        )],
    }
    .build();
    Circuit::from_raw(p, raw)
}

/// A standalone statement of a mixed split participant: `ZkStatement`, then
/// the frontend's `Circuit`, `CommitmentLayout`, `JointGeometry` and
/// `PublicInputs`, in the order and with the writers of `ZkProofStatement`.
struct SplitStatement<'a> {
    identity: ZkStatement<'a>,
    part: FrontendPart<'a, P256Field, MixedSplit<P256Field>>,
}
impl<'a> Statement for SplitStatement<'a> {
    type Identity = ZkStatement<'a>;
    fn identity(&self) -> &ZkStatement<'a> {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.part.write_circuits(h);
        self.part.write_layout(h);
        write_joint_geometry(h, CONFIG);
        self.part.write_public(h);
    }
}

/// The statement of a mixed split P-256 participant of `circuit` whose values
/// `foreign` are bit groups and whose mask R is `mask`, and its storage.
fn split_statement(
    circuit: &Circuit<P256Field>,
    foreign: &[(usize, Group)],
    mask: Group,
) -> (Vec<u8>, MixedStorage) {
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let d = QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    let storage = StorageMap::new(value_count(circuit).unwrap(), foreign).unwrap();
    let participant = MixedSplit::new(circuit, storage, mask, CONFIG, &d).unwrap();
    let public = [p.one()];
    let statement = SplitStatement {
        identity: ZkStatement { context: CONTEXT },
        part: FrontendPart::new(&participant, &[circuit], &public).unwrap(),
    };
    let split = participant.fields_for_test().2.clone();
    (statement_bytes(&statement), split)
}

/// The fields of `b`'s runs that differ from `a`'s, run by run, if both
/// have the same number of runs of the same kinds.
fn changed_run_fields(a: &[Run], b: &[Run]) -> Option<BTreeSet<&'static str>> {
    if a.len() != b.len() {
        return None;
    }
    let mut out = BTreeSet::new();
    for pair in a.iter().zip(b) {
        let fields: Vec<(&str, usize, usize)> = match pair {
            (
                Run::Native { first, count, cell },
                Run::Native {
                    first: f,
                    count: c,
                    cell: x,
                },
            ) => vec![
                ("Native.first", *first, *f),
                ("Native.count", *count, *c),
                ("Native.cell", *cell, *x),
            ],
            (
                Run::Prime {
                    first,
                    count,
                    start,
                    width,
                },
                Run::Prime {
                    first: f,
                    count: c,
                    start: s,
                    width: w,
                },
            ) => vec![
                ("Prime.first", *first, *f),
                ("Prime.count", *count, *c),
                ("Prime.start", *start, *s),
                ("Prime.width", *width, *w),
            ],
            // No wildcard: a new kind of run does not compile until it is
            // covered here.
            (Run::Native { .. }, Run::Prime { .. }) | (Run::Prime { .. }, Run::Native { .. }) => {
                return None
            }
        };
        out.extend(
            fields
                .into_iter()
                .filter(|(_, x, y)| x != y)
                .map(|(n, ..)| n),
        );
    }
    Some(out)
}

#[test]
fn storage_fields_are_absorbed() {
    let p = P256Field::new();
    let circuit = prime_circuit(&p, 5);
    let group = |start, width| Group::new(start, width).unwrap();
    let mask = group(100, 256);
    let (base, split) = split_statement(&circuit, &[(1, group(10, 8))], mask);
    let MixedStorage {
        map,
        mask: r,
        mask_cell,
    } = &split;
    let (entries, native) = map.fields_for_test();
    let runs = map.runs();
    let [r_start, r_width] = r.fields_for_test();
    // MixedStorage.mask, written: R's start and width.
    for other in [group(r_start + 1, r_width), group(r_start, r_width - 1)] {
        let (bytes, s) = split_statement(&circuit, &[(1, group(10, 8))], other);
        assert_eq!(s.mask, other);
        assert_ne!(bytes, base, "mask {other:?}");
    }
    // StorageMap.entries, each element: every private value but the
    // foreign one made foreign too, and the foreign one's group (start and
    // width, each written in the stored runs). The foreign value cannot
    // become native: a split needs a foreign value. Pads cannot become
    // foreign: mixed storage keeps every pad native (`MixedStorage::new`).
    let private = circuit.raw.ninput - circuit.raw.npublic_input;
    assert!(matches!(entries[1], Storage::Foreign(_)));
    assert!(entries[private..]
        .iter()
        .all(|e| matches!(e, Storage::Native(_))));
    let mut covered = BTreeSet::new();
    let mut variants: Vec<Vec<(usize, Group)>> = (0..private)
        .filter(|&v| v != 1)
        .map(|v| vec![(1, group(10, 8)), (v, group(20, 8))])
        .collect();
    variants.extend([
        vec![(1, group(11, 8))],
        vec![(1, group(10, 7))],
        vec![(2, group(10, 8))],
        vec![(1, group(10, 8)), (2, group(18, 8))],
    ]);
    for foreign in &variants {
        let (bytes, s) = split_statement(&circuit, foreign, mask);
        assert_ne!(s.map.fields_for_test().0, entries);
        assert_ne!(bytes, base, "foreign {foreign:?}");
        let other = s.map.runs();
        covered.extend(changed_run_fields(&runs, &other).unwrap_or_default());
        // StorageMap.native and MixedStorage.mask_cell, derived: the native count,
        // and R's cell after every native value, move with the entries.
        if foreign.len() > 1 {
            assert_ne!(
                (s.map.fields_for_test().1, s.mask_cell),
                (native, *mask_cell)
            );
        }
    }
    // Every run field, written, changed in some variant.
    let all = [
        "Native.cell",
        "Native.count",
        "Native.first",
        "Prime.count",
        "Prime.first",
        "Prime.start",
        "Prime.width",
    ];
    assert_eq!(covered, BTreeSet::from(all));
}
