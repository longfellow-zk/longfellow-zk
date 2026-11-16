// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! A composed statement holds every value the composed verifier uses
//! (transcript I1, I3): both frontends, the adapter and the joint geometry.
use super::{
    super::{ComposedStatement, Composition},
    circuit, Mode, CONFIG, LABEL, WIDTH,
};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            packing::PackingField,
            range_interpolation::{
                BinaryInterpolatorFactory, EvaluationDomain,
                QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT, ZkField,
        },
        v2::{
            foreign::adapter::AdapterMode,
            proto::{
                composed::ComposedGeometry,
                tests::statement::{Identity, Statement},
            },
            transcript::{Opened, SetupMessage, ZkStatement, ZK_PROTOCOL_ID},
            zk::{
                split::value_count,
                storage::{Group, StorageMap},
            },
        },
    },
};

impl<F, DH, DS, M, I> ComposedStatement<'_, F, DH, DS, M, I>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<super::super::Host>,
    DS: EvaluationDomain<F>,
    M: AdapterMode<F>,
    I: SetupMessage,
{
    /// Check every value of this statement that the composed verifier and
    /// the proof reader use against the statement `d` decoded from the
    /// transcript, except the identity, which the application checks, and
    /// the mode's own layout, which `check_mode` checks.
    ///
    /// The evaluation domains are not statement values: the verifier fixes
    /// them (`polygero::param`), and each participant rejects a domain other
    /// than the one its parameter was validated against.
    pub(crate) fn check_absorbed_for_test(&self, d: &Statement, check_mode: impl FnOnce(&M)) {
        let ComposedStatement {
            identity: _,
            composition,
            host,
            split,
            geometry,
        } = self;
        let Composition {
            host_circuit,
            split_circuit,
            domains: _,
            host: host_participant,
            split: split_participant,
            suffix,
            mask,
            mode,
        } = composition;
        // The frontend parts read the composition's participants and
        // circuits: the host circuit and the mode's fragment, then the split
        // circuit.
        let (host_part, host_circuits, _) = host.fields_for_test();
        let (split_part, split_circuits, _) = split.fields_for_test();
        assert!(std::ptr::eq(host_part, host_participant));
        assert!(std::ptr::eq(split_part, split_participant));
        let [h, fragment] = host_circuits else {
            panic!("the host proves its circuit and the fragment")
        };
        assert!(std::ptr::eq(*h, *host_circuit));
        assert!(std::ptr::eq(*fragment, mode.fragment()));
        let [s] = split_circuits else {
            panic!("the split participant proves one circuit")
        };
        assert!(std::ptr::eq(*s, *split_circuit));
        assert_eq!(d.circuits.len(), 3);
        assert_eq!(
            (d.layouts.len(), d.public.len(), d.adapters.len()),
            (2, 2, 1)
        );
        let config = d.config();
        let a = &d.adapters[0];
        let leaves = usize::try_from(a.trees * a.leaves).unwrap();
        assert_eq!(mode.virtual_inputs(), leaves, "virtual leaves");
        let gh = host.check_absorbed_for_test(
            &d.circuits[..2],
            &d.layouts[0],
            &d.public[0],
            config,
            leaves,
        );
        let gs =
            split.check_absorbed_for_test(&d.circuits[2..], &d.layouts[1], &d.public[1], config, 0);
        assert_eq!(
            ComposedGeometry::new(gh, gs, config).unwrap(),
            *geometry,
            "the proof geometry is the one the statement determines"
        );
        assert_eq!(composition.param().unwrap().config(), config);
        // The reserved suffix follows the host circuit's inputs and starts
        // with R, whose bits the split layout holds.
        assert_eq!(suffix.start(), host_circuit.raw.ninput);
        assert_eq!(mask.start(), suffix.start());
        assert_eq!(
            [mask.start(), mask.width()].map(|x| x as u64),
            d.layouts[1].mask
        );
        check_mode(mode);
    }
}

/// The statement of the tiny composition (the parent module's circuits),
/// decoded from the verifier's session right after it opened, holds every
/// value the composed verifier uses; the session then verifies its proof.
#[test]
fn composed_statement_round_trip() {
    let gf2 = Gf2_128Field::new();
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let host_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let split_domain =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    let host = circuit(&gf2, 1 + WIDTH, vec![gf2.one()], &[(0, 0), (1, 0)]);
    let split = circuit(&p, 3, vec![p.one(), p.mone()], &[(1, 0), (2, 1)]);
    let shared = Group::new(1, WIDTH).unwrap();
    let storage = StorageMap::new(value_count(&split).unwrap(), &[(0, shared)]).unwrap();
    let c = Composition::<P256Field, _, _, Mode>::new(
        &host,
        &split,
        storage,
        CONFIG,
        (&host_domain, &split_domain),
    )
    .unwrap();
    let split_public = [p.one()];
    let statement = c
        .statement(ZkStatement { context: LABEL }, &[true], &split_public)
        .unwrap();
    let x = 0xa5u64;
    let bits: Vec<bool> = (0..WIDTH).map(|j| (x >> j) & 1 != 0).collect();
    let value = crate::core::algebra::SupportsU64Conversions::u64_to_element(&p, x);
    let (proof, _) = ComposedStatement::prove(
        Opened::new(&statement),
        bits,
        vec![value, value],
        &mut crate::runtime::random::DeterministicRng::new(5),
    )
    .unwrap();
    let session = Opened::new(&statement);
    let d = Statement::from_statement_bytes(session.statement_bytes_for_test());
    assert_eq!(
        d.identity,
        Identity::Zk {
            protocol: ZK_PROTOCOL_ID.to_vec(),
            context: LABEL.to_vec()
        }
    );
    session
        .statement()
        .check_absorbed_for_test(&d, |mode| mode.check_absorbed_for_test(&d));
    ComposedStatement::reduce_and_authenticate(session, &proof).unwrap();
}
