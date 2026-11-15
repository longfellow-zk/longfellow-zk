// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The statement holds every value the verifier uses (transcript I1, I3).
//!
//! The round-trip checks decode the statement from the bytes the verifier
//! hashed, rebuild from those values alone every instance value the
//! verifier reads (its circuits through their IDs, which hash their whole
//! content, then the input layout, the storage map, the commitment layout,
//! the cell count and the proof geometry), and compare them with the values
//! of the statement object the verifier was opened with.
use super::{circuit, prove_standalone};
use crate::{
    core::{algebra::AlgebraicField, proto::v2::compute_id},
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        random::DeterministicRng,
        v2::{
            proto::{
                polygero::{PolygeroConfig, PolygeroGeometry},
                tests::statement::{Identity, Layout, Public, Statement},
                witness_selection::FINGERPRINTS,
                zk::{CircuitGeometry, ZkProof, ZkProofGeometry},
            },
            sumcheck::circuit_geometry,
            transcript::{Opened, ZkStatement, ZK_PROTOCOL_ID},
            witness_selection::witness_count,
            zk::{
                joint::FrontendPart,
                packing_commitment::{PackingCommitment, PackingLayout},
                storage::{Group, Run, Split, StorageMap},
                InputLayout, ZkContext, ZkProofStatement, ZkProver, ZkVerifier,
            },
        },
    },
};

/// The split storage a `CommitmentLayout` describes, rebuilt from its runs
/// alone: `private` private inputs then `pads` pads, the stored runs' values
/// as bit groups, every other value native in value order, and R's bits.
fn rebuild_split(layout: &Layout, private: usize, pads: usize) -> Split {
    let values = usize::try_from(layout.values()).unwrap();
    assert_eq!(values, private + pads, "the runs cover every value");
    let mut foreign = Vec::new();
    for &[first, count, start, width] in &layout.stored {
        for i in 0..count {
            let group = Group::new((start + i * width) as usize, width as usize).unwrap();
            foreign.push(((first + i) as usize, group));
        }
    }
    let map = StorageMap::new(values, &foreign).unwrap();
    // The runs are the map's canonical encoding: native cells are dense in
    // value order, so the absorbed native runs are the rebuilt map's.
    let (mut native, mut stored) = (Vec::new(), Vec::new());
    for run in map.runs() {
        match run {
            Run::Native { first, count, cell } => {
                native.push([first, count, cell].map(|x| x as u64))
            }
            Run::Prime {
                first,
                count,
                start,
                width,
            } => stored.push([first, count, start, width].map(|x| x as u64)),
        }
    }
    assert_eq!(
        (native, stored),
        (layout.native.clone(), layout.stored.clone())
    );
    let mask = if map.is_pure_foreign() {
        assert_eq!(layout.mask, [0, 0], "pure foreign storage has no mask");
        None
    } else {
        Some(Group::new(layout.mask[0] as usize, layout.mask[1] as usize).unwrap())
    };
    Split::new(map, mask, private, values).unwrap()
}

impl<const W: usize, F: ZkField<W> + PackingField> FrontendPart<'_, W, F> {
    /// Check this frontend part, as the verifier reads it, against its
    /// decoded statement values: the IDs of its circuits, its commitment
    /// layout and its public inputs, under the profile `config` and with
    /// `virtual_inputs` virtual inputs (the adapter's leaves, from its
    /// `AdapterLayout`). Returns the circuit geometry rebuilt from them.
    pub(crate) fn check_absorbed_for_test(
        &self,
        ids: &[[u8; 32]],
        layout: &Layout,
        public: &Public,
        config: PolygeroConfig,
        virtual_inputs: usize,
    ) -> CircuitGeometry {
        let FrontendPart {
            participant,
            circuits,
            public: values,
        } = self;
        let (geometry, prover_config, param, backend, id, additional_ids, inputs, storage) =
            participant.fields_for_test();
        let PackingCommitment {
            parameters,
            layout: cells,
        } = backend;
        let f = parameters.field();
        // The circuits are the ones the IDs name, and each ID is the hash of
        // its circuit's whole content (field, counts, layers, constants), so
        // the IDs bind every circuit value the verifier reads.
        let named: Vec<[u8; 32]> = circuits.iter().map(|c| c.id).collect();
        assert_eq!(named, ids, "circuit IDs");
        for c in circuits {
            assert_eq!(compute_id(f, &c.raw), c.id, "the ID hashes the circuit");
        }
        assert_eq!((id, additional_ids), (&ids[0], &ids[1..]));
        assert_eq!(layout.field, f.field_id() as u64, "layout FieldID");
        assert_eq!(public.field, layout.field, "public input FieldID");
        // The public inputs, as the circuit's field elements.
        assert_eq!(public.elements.len(), circuits[0].raw.npublic_input);
        let encoded: Vec<Vec<u8>> = values.iter().map(|x| f.to_bytes(x)).collect();
        assert_eq!(public.elements, encoded, "public inputs");
        // The packing descriptor is written whole and carries the degree.
        assert_eq!(layout.descriptor, parameters.descriptor(), "descriptor");
        let descriptor = layout.descriptor();
        assert_eq!(descriptor.packing, f.packing_id());
        assert_eq!(descriptor.embedding, parameters.extension().embedding_id());
        let degree = usize::try_from(descriptor.degree).unwrap();
        assert_eq!(degree, parameters.degree());
        // The shared input array follows from the circuits and the virtual
        // input count; the sumcheck geometry and its pads from the circuits.
        let shared = InputLayout::new(circuits, virtual_inputs).unwrap();
        assert_eq!(shared, *inputs, "input layout");
        let sumcheck = circuit_geometry(circuits).unwrap();
        let commits = participant.commits();
        let (private, pads) = (layout.private as usize, layout.pads as usize);
        if commits {
            assert_eq!(pads, sumcheck.pad_count(), "pad cells");
            assert_eq!(layout.masks as usize, FINGERPRINTS, "fingerprint masks");
        } else {
            assert_eq!([layout.private, layout.pads, layout.masks], [0; 3]);
        }
        // The storage map, R's bits and R's cell (after every native value).
        let mask_cells = match storage {
            None => {
                assert!(layout.native.is_empty() && layout.stored.is_empty());
                assert_eq!(layout.mask, [0, 0]);
                assert_eq!(private, shared.committed(), "committed private inputs");
                0
            }
            Some(split) => {
                let rebuilt = rebuild_split(layout, shared.committed(), sumcheck.pad_count());
                assert_eq!(rebuilt, *split, "split storage");
                if commits {
                    assert_eq!(private + pads, layout.native_cells() as usize);
                    assert_eq!(split.mask_cell, layout.native_cells() as usize);
                }
                usize::from(split.mask.is_some())
            }
        };
        // The commitment layout from the absorbed counts and degree, then
        // the committed cell count with R's cell and the fingerprint masks.
        let rebuilt_cells = PackingLayout::new(private, pads, degree).unwrap();
        assert_eq!(rebuilt_cells, *cells, "commitment layout");
        let nw = if commits {
            witness_count(rebuilt_cells.witness_count + mask_cells).unwrap()
        } else {
            0
        };
        let rebuilt = CircuitGeometry::new(sumcheck, degree, nw).unwrap();
        assert_eq!(rebuilt, *geometry, "circuit geometry");
        assert_eq!(
            param.as_ref().map(|p| p.geometry()),
            commits.then(|| PolygeroGeometry::new(nw, config).unwrap()),
            "Polygero geometry"
        );
        assert_eq!(*prover_config, config);
        rebuilt
    }
}

impl<const W: usize, F: ZkField<W> + PackingField> ZkProofStatement<'_, W, F> {
    /// Check every value of this statement, as the verifier reads it,
    /// against the statement `d` decoded from the transcript.
    pub(crate) fn check_absorbed_for_test(&self, d: &Statement) {
        let ZkProofStatement {
            identity: ZkStatement { context },
            part,
            geometry,
        } = self;
        let identity = Identity::Zk {
            protocol: ZK_PROTOCOL_ID.to_vec(),
            context: context.to_vec(),
        };
        assert_eq!(d.identity, identity);
        assert!(d.adapters.is_empty());
        assert_eq!((d.layouts.len(), d.public.len()), (1, 1));
        let config = d.config();
        let circuit =
            part.check_absorbed_for_test(&d.circuits, &d.layouts[0], &d.public[0], config, 0);
        assert_eq!(
            ZkProofGeometry::new(circuit, config).unwrap(),
            *geometry,
            "the proof geometry is the one the statement determines"
        );
    }
}

const CONTEXT: &[u8] = b"longfellow/v2/test/absorption";

/// Prove and completely verify the standalone test circuit, decode the
/// statement from the verifier's own trace, and check it against the
/// statement and geometry the verifier was opened with.
fn round_trip<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    f: &F,
    domain: &D,
) {
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let ctx = ZkContext::new(domain);
    let extension = f.packing_extension();
    let base = extension.base();
    let public = vec![base.one()];
    let prover = ZkProver::new(circuit(f), config, &ctx).unwrap();
    let (proof, geometry, t) = prove_standalone(
        &prover,
        CONTEXT,
        &public,
        vec![base.one(), base.one()],
        &ctx,
        &mut DeterministicRng::new(42),
    )
    .unwrap();
    let encoded = proof.write(&geometry, f, t).unwrap();
    let verifier = ZkVerifier::new(circuit(f), config, &ctx).unwrap();
    let statement = verifier.statement(CONTEXT, &public).unwrap();
    let mut session = Opened::new(&statement);
    let used = session.statement();
    let opened = Statement::from_statement_bytes(session.statement_bytes_for_test());
    let parsed = {
        let g = session.geometry();
        assert!(std::ptr::eq(g.part(), &used.geometry));
        ZkProof::read(encoded.as_bytes(), &g, f).unwrap()
    };
    let verified = verifier.verify(session, parsed, &ctx).unwrap();
    let decoded = Statement::from_trace(&verified.trace);
    assert_eq!(decoded, opened);
    used.check_absorbed_for_test(&decoded);
    assert_eq!(verifier.geometry(), used.geometry);
}

#[test]
fn binary_statement_round_trip() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    round_trip(&f, &BinaryInterpolatorFactory::full_field(&f));
}

#[test]
fn prime_statement_round_trip() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    round_trip(
        &f,
        &QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order()),
    );
}
