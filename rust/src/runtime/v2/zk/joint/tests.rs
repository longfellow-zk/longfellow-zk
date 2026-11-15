// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, Sealed, SerializableField, SupportsU64Conversions},
        proto::v2::{self, Constant, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{
            fp_generic::FpGenericField, gf2_128::Gf2_128Field, limb::LIMBS_PER_U64,
            p256::P256Field, range_interpolation::BinaryInterpolatorFactory, RuntimeField,
        },
        random::DeterministicRng,
        v2::{
            proto::{dual_packing::PackingProof, zk::CircuitProof},
            sumcheck::eval_circuit,
            transcript::{SessionStamp, Transcript},
            zk::{self, VirtualInputs},
        },
    },
};

/// Draw `t`'s top weights, then prove its frontend.
fn prove<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    state: crate::runtime::v2::zk::prover::CircuitState<W, F>,
    virtual_inputs: &VirtualInputs<F::E>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<
    (
        CircuitProof<W, F>,
        crate::runtime::v2::polygero::LinearStatement<F::E>,
    ),
    String,
> {
    let top = top_weights(t)?;
    zk::prove(t, state, top, virtual_inputs, ctx)
}

/// Draw `t`'s top weights, then reduce its frontend.
fn reduce<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
    proof: &CircuitProof<W, F>,
    virtual_inputs: &VirtualInputs<F::E>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<crate::runtime::v2::polygero::LinearStatement<F::E>, String> {
    let top = top_weights(t)?;
    zk::reduce(t, proof, top, virtual_inputs, ctx)
}

#[test]
fn selected_joint_wrapper_supports_three_typed_fields() {
    use crate::runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory},
        v2::{
            polygero::LinearStatement,
            proto::polygero::PolygeroConfig,
            transcript::Transcript,
            zk::joint::{JointParam, SelectedField},
        },
    };
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let pd = ScalarInterpolatorFactory::new(&p, 72);
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let a = SelectedField::new(2, config, &d).unwrap();
    assert_eq!(a.geometry().nw, 4);
    let param = JointParam::new((
        a,
        (
            SelectedField::new(1, config, &pd).unwrap(),
            (SelectedField::new(0, config, &d).unwrap(), ()),
        ),
    ))
    .unwrap();
    // Empty frontend systems, derived on the session `session` names.
    let statements = |session: SessionStamp| {
        let empty = || LinearStatement {
            a: vec![],
            b: vec![],
            session: session.clone(),
        };
        let prime = LinearStatement {
            a: vec![],
            b: vec![],
            session: session.clone(),
        };
        (empty(), (prime, (empty(), ())))
    };
    let tp = Transcript::for_test(b"zk-v2/selected-three-fields");
    let (mut prover, root, responses) = param
        .commit(
            (vec![f.one(), f.zero()], (vec![p.one()], (vec![], ()))),
            tp,
            &mut DeterministicRng::new(91),
        )
        .unwrap();
    let equations = statements(prover.bound(&()).session());
    let (proof, mut tp) = prover.finish(&param, equations).unwrap();
    let verify = |responses| {
        let tv = Transcript::for_test(b"zk-v2/selected-three-fields");
        let mut verifier = param.clone().receive(&root, responses, tv);
        let verifier_equations = statements(verifier.bound(&()).session());
        verifier.finish(verifier_equations, &proof)
    };
    let mut tv = verify(responses.clone()).unwrap().into_transcript();
    assert_eq!(tp.bytes(32), tv.bytes(32));
    let mut altered = responses;
    f.add(&mut altered.1 .1 .0.values[1], &f.one());
    assert!(verify(altered).is_err());
}
/// `finish` accepts only equations derived on its own session: neither a
/// system derived on another session with the same history (a fork) nor a
/// static system (`LinearStatement::new`), in either role.
#[test]
fn finish_rejects_equations_derived_on_another_session() {
    use crate::runtime::v2::{
        polygero::LinearStatement,
        proto::polygero::PolygeroConfig,
        zk::joint::{JointParam, SelectedField},
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let param = JointParam::new((SelectedField::new(2, config, &d).unwrap(), ())).unwrap();
    let derived = |session| {
        (
            LinearStatement {
                a: vec![],
                b: vec![],
                session,
            },
            (),
        )
    };
    let commit = || {
        param
            .commit(
                (vec![f.one(), f.zero()], ()),
                Transcript::for_test(b"zk-v2/stamp"),
                &mut DeterministicRng::new(5),
            )
            .unwrap()
    };
    const ERROR: &str = "frontend equations derived on another session";
    let (mut forked_prover, _, _) = commit();
    let prover_fork = forked_prover
        .transcript()
        .fork_for_test()
        .session_for_test();
    assert_eq!(
        forked_prover
            .finish(&param, derived(prover_fork))
            .err()
            .unwrap(),
        ERROR
    );
    let (static_prover, _, _) = commit();
    let prover_fixed = (LinearStatement::new(vec![], vec![]), ());
    assert_eq!(
        static_prover.finish(&param, prover_fixed).err().unwrap(),
        ERROR
    );

    let (mut prover, root, responses) = commit();
    let prover_equations = derived(prover.bound(&()).session());
    let (proof, _) = prover.finish(&param, prover_equations).unwrap();
    let receive = || {
        param.clone().receive(
            &root,
            responses.clone(),
            Transcript::for_test(b"zk-v2/stamp"),
        )
    };
    let mut forked_verifier = receive();
    let verifier_fork = forked_verifier
        .transcript()
        .fork_for_test()
        .session_for_test();
    assert_eq!(
        forked_verifier
            .finish(derived(verifier_fork), &proof)
            .err()
            .unwrap(),
        ERROR
    );
    let verifier_fixed = (LinearStatement::new(vec![], vec![]), ());
    assert_eq!(
        receive().finish(verifier_fixed, &proof).err().unwrap(),
        ERROR
    );
    let mut verifier = receive();
    let verifier_equations = derived(verifier.bound(&()).session());
    verifier.finish(verifier_equations, &proof).unwrap();
}
fn circuits<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
) -> (Circuit<F>, Circuit<F>) {
    let layer = |nw, q, l| {
        Layer::new(
            nw,
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::default(),
        )
    };
    let circuit = |layers| {
        let raw = RawCircuitBuilder {
            ninput: 4,
            npublic_input: 1,
            noutput: 1,
            logv: 0,
            constants: vec![f.zero(), f.one(), f.mone()],
            layers,
        }
        .build();
        Circuit::from_raw(f, raw)
    };
    (
        circuit(vec![layer(
            4,
            vec![Quadratic {
                g: 0,
                l: 1,
                r: 2,
                k: 1,
            }],
            vec![Linear { g: 0, l: 0, k: 2 }, Linear { g: 0, l: 3, k: 0 }],
        )]),
        circuit(vec![
            layer(
                3,
                vec![],
                vec![
                    Linear { g: 0, l: 0, k: 2 },
                    Linear { g: 0, l: 1, k: 1 },
                    Linear { g: 0, l: 2, k: 0 },
                ],
            ),
            layer(
                4,
                vec![Quadratic {
                    g: 1,
                    l: 1,
                    r: 2,
                    k: 1,
                }],
                vec![Linear { g: 0, l: 0, k: 1 }, Linear { g: 2, l: 3, k: 1 }],
            ),
        ]),
    )
}

/// A frontend part takes only its participant's circuits: the same IDs, in
/// the same order and number. Circuits with another ID but the same layout
/// are rejected, as are a missing, an extra or a reordered circuit.
#[test]
fn frontend_part_takes_only_its_participants_circuits() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let ctx = ZkContext::new(&domain);
    let (main, side) = circuits(&f);
    let config = PolygeroConfig {
        k: 64,
        s: 2,
        n: 256,
        t: 8,
    };
    let p = CircuitParticipant::new(&[&main, &side], 0, config, &ctx).unwrap();
    let renamed = |c: Circuit<Gf2_128Field>| {
        let mut id = c.id;
        id[0] ^= 1;
        Circuit::with_test_id(id, c.into_raw())
    };
    let (main_copy, side_copy) = circuits(&f);
    let (other_main, other_side) = (renamed(main_copy), renamed(side_copy));
    assert!(FrontendPart::new(&p, &[&main, &side], &[true]).is_ok());
    for list in [
        vec![&other_main, &side],
        vec![&main, &other_side],
        vec![&main],
        vec![&main, &side, &side],
        vec![&side, &main],
    ] {
        assert_eq!(
            FrontendPart::new(&p, &list, &[true]).err().unwrap(),
            "circuit statement mismatch"
        );
    }
}

#[test]
fn binary_circuits_authenticate_one_shared_input() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let ctx = ZkContext::new(&domain);
    let (main, side) = circuits(&f);
    let config = PolygeroConfig {
        k: 64,
        s: 2,
        n: 256,
        t: 8,
    };
    for count in [0, 1, 3, 5] {
        let mut components = vec![&main];
        components.extend(vec![&side; count]);
        let p = CircuitParticipant::new(&components, 0, config, &ctx).unwrap();
        let private = vec![true, true, false];
        let mut rng = DeterministicRng::new(77);
        let (state, w) = p.prepare(private.to_vec(), &mut rng).unwrap();
        // Circuit multiplicity changes pads, but never duplicates the packed input.
        assert_eq!(p.backend.layout.private_inputs, 3);
        let param =
            crate::runtime::v2::zk::joint::JointParam::new((p.participant(&ctx).unwrap(), ()))
                .unwrap();
        let t = Transcript::for_test(b"fragmented-pcs-test");
        let (mut joint, root, responses) = param.commit((w, ()), t, &mut rng).unwrap();
        let (proof, statement) = prove(
            &mut joint.bound(&FrontendPart::new(&p, &components, &[true]).unwrap()),
            state,
            &VirtualInputs::none(),
            &ctx,
        )
        .unwrap();
        let (opening, _) = joint.finish(&param, (statement, ())).unwrap();
        let verify = |candidate: &CircuitProof<2, Gf2_128Field>, public: bool| {
            let t = Transcript::for_test(b"fragmented-pcs-test");
            let mut v = param.clone().receive(&root, responses.clone(), t);
            let statement = reduce(
                &mut v.bound(&FrontendPart::new(&p, &components, &[public])?),
                candidate,
                &VirtualInputs::none(),
                &ctx,
            )?;
            v.finish((statement, ()), &opening)
                .map(|_| ())
                .map_err(|e| e.to_string())
        };
        verify(&proof, true).unwrap();
        assert!(verify(&proof, false).is_err());
        let mut changed = proof.clone();
        f.add(&mut changed.sumcheck_proof.layers[0].claims[1], &f.one());
        assert!(verify(&changed, true).is_err());
        if count > 0 {
            let (_, wrong) = circuits(&f);
            let id = wrong.id;
            let mut raw = wrong.into_raw().into_builder();
            raw.ninput += 1;
            let wrong = Circuit::with_test_id(id, raw.build());
            let mut invalid = vec![&main];
            invalid.extend(vec![&wrong; count]);
            // No frontend part, and so no transcript use, for a mismatched layout.
            assert!(FrontendPart::new(&p, &invalid, &[true]).is_err());
            assert!(CircuitParticipant::new(&invalid, 0, config, &ctx).is_err());
        }
    }
}
#[test]
fn prime_direct_packing_uses_the_owned_committed_witness() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let domain =
        QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    let ctx = ZkContext::new(&domain);
    let (main, side) = circuits(&f);
    let components = [&main, &side, &main];
    let p = CircuitParticipant::new(
        &components,
        0,
        PolygeroConfig {
            k: 64,
            s: 2,
            n: 256,
            t: 8,
        },
        &ctx,
    )
    .unwrap();
    let mut private = [2, 3, 0].map(|x| f.u64_to_element(x)).to_vec();
    let public = [f.u64_to_element(6)];
    let mut rng = DeterministicRng::new(78);
    let (state, w) = p.prepare(private.to_vec(), &mut rng).unwrap();
    assert_eq!(p.geometry().packing_degree(), 1);
    assert_eq!(w.len(), private.len() + p.geometry().sumcheck().pad_count());
    // The prover can no longer substitute these values for the committed ones.
    // The state owns its inputs; the original caller's buffer is unrelated.
    private[0] = f.zero();
    let mut substituted = public.to_vec();
    substituted.extend(private);
    assert!(eval_circuit(substituted, &main, &f).is_err());
    let param =
        crate::runtime::v2::zk::joint::JointParam::new((p.participant(&ctx).unwrap(), ())).unwrap();
    let t = Transcript::for_test(b"prime-fragmented-pcs-test");
    let (mut joint, root, responses) = param.commit((w, ()), t, &mut rng).unwrap();
    let (proof, statement) = prove(
        &mut joint.bound(&FrontendPart::new(&p, &components, &public).unwrap()),
        state,
        &VirtualInputs::none(),
        &ctx,
    )
    .unwrap();
    assert!(matches!(proof.packing, PackingProof::Direct));
    let (opening, mut tp) = joint.finish(&param, (statement, ())).unwrap();
    let t = Transcript::for_test(b"prime-fragmented-pcs-test");
    let mut v = param.receive(&root, responses, t);
    let statement = reduce(
        &mut v.bound(&FrontendPart::new(&p, &components, &public).unwrap()),
        &proof,
        &VirtualInputs::none(),
        &ctx,
    )
    .unwrap();
    let mut tv = v
        .finish((statement, ()), &opening)
        .unwrap()
        .into_transcript();
    assert_eq!(tp.bytes(32), tv.bytes(32));
}

#[test]
fn malformed_public_prefix_is_an_error_before_sampling() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let raw = RawCircuitBuilder {
        ninput: 0,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![],
        layers: vec![],
    }
    .build();
    let circuit = v2::Circuit::with_test_id([0; 32], raw);
    let result = crate::runtime::v2::zk::ZkProver::new(
        circuit,
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
        &ZkContext::new(&domain),
    );
    assert!(matches!(result, Err(ref e) if e == "public prefix"));
}

#[test]
fn final_seal_failure_has_its_own_verification_error() {
    use crate::runtime::v2::{
        proto::zk::ZkProof,
        transcript::Opened,
        zk::{ZkProver, ZkVerificationError, ZkVerifier},
    };
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let context = ZkContext::new(&domain);
    let (circuit, _) = circuits(&f);
    let config = PolygeroConfig {
        k: 64,
        s: 4,
        n: 448,
        t: 24,
    };
    let prover = ZkProver::new(circuit, config, &context).unwrap();
    let private = vec![false; 3];
    let statement = prover.statement(b"seal error", &[false]).unwrap();
    let committed = prover
        .commit(
            private.to_vec(),
            &statement,
            &context,
            &mut DeterministicRng::new(45),
        )
        .unwrap();
    let (proof, transcript) = prover.prove(committed, &context).unwrap();
    let mut bytes = proof
        .write(&statement.geometry, &f, transcript)
        .unwrap()
        .into_bytes();
    drop(statement);
    let verifier = ZkVerifier::new(prover.circuit, config, &context).unwrap();
    let check = |bytes: &[u8]| {
        let statement = verifier.statement(b"seal error", &[false]).unwrap();
        let mut session = Opened::new(&statement);
        let decoded = ZkProof::read(bytes, &session.bound(|s| &s.geometry), &f).unwrap();
        verifier.verify(session, decoded, &context).map(|_| ())
    };
    check(&bytes).unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    assert!(matches!(
        check(&bytes),
        Err(ZkVerificationError::InvalidTranscriptSeal(_))
    ));
}

/// A fragment reading `virt = c0 + c1 * x[1]` beyond the primary circuit's
/// inputs. The virtual entry is substituted at constraint compilation; only the
/// three private inputs are committed.
#[test]
fn binary_virtual_inputs_are_substituted_not_committed() {
    use crate::{core::algebra::SupportsU128Conversions, runtime::v2::zk::VirtualInput};
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let ctx = ZkContext::new(&domain);
    let (main, _) = circuits(&f);
    // Output: in[4] + 1, which vanishes iff the virtual entry equals one.
    let fragment = Circuit::from_raw(
        &f,
        RawCircuitBuilder {
            ninput: 5,
            npublic_input: 1,
            noutput: 1,
            logv: 0,
            constants: vec![f.zero(), f.one()],
            layers: vec![Layer::new(
                5,
                Stream::default(),
                Stream::<Linear>::from_terms([Linear { g: 0, l: 4, k: 1 }]),
                Stream::<Constant>::from_terms([Constant { g: 0, k: 1 }]),
            )],
        }
        .build(),
    );
    let config = PolygeroConfig {
        k: 64,
        s: 2,
        n: 256,
        t: 8,
    };
    let p = CircuitParticipant::new(&[&main, &fragment], 1, config, &ctx).unwrap();
    assert_eq!(p.backend.layout.private_inputs, 3);
    assert_eq!((p.inputs.committed_end, p.inputs.ninput), (4, 5));
    // x[1] = 1, so c0 + c1 = 1 makes the virtual entry one.
    let c0 = f.u128_to_element(7);
    let definition = |c0| VirtualInputs {
        entries: vec![VirtualInput {
            source: 1,
            constant: c0,
            coefficient: f.addf(&c0, &f.one()),
        }],
    };
    let honest = definition(c0);
    let param =
        crate::runtime::v2::zk::joint::JointParam::new((p.participant(&ctx).unwrap(), ())).unwrap();
    let mut rng = DeterministicRng::new(91);
    let (state, w) = p.prepare(vec![true, true, false], &mut rng).unwrap();
    let t = Transcript::for_test(b"virtual-inputs-test");
    let (mut joint, root, responses) = param.commit((w, ()), t, &mut rng).unwrap();
    let (proof, statement) = prove(
        &mut joint.bound(&FrontendPart::new(&p, &[&main, &fragment], &[true]).unwrap()),
        state,
        &honest,
        &ctx,
    )
    .unwrap();
    let (opening, _) = joint.finish(&param, (statement, ())).unwrap();
    let verify = |definition: &VirtualInputs<_>| {
        let t = Transcript::for_test(b"virtual-inputs-test");
        let mut v = param.clone().receive(&root, responses.clone(), t);
        let statement = reduce(
            &mut v.bound(&FrontendPart::new(&p, &[&main, &fragment], &[true])?),
            &proof,
            definition,
            &ctx,
        )?;
        v.finish((statement, ()), &opening)
            .map(|_| ())
            .map_err(|e| e.to_string())
    };
    verify(&honest).unwrap();
    // A different definition, even one that also equals one at x[1] = 1,
    // changes the compiled statement and fails authentication.
    assert!(verify(&definition(f.u128_to_element(9))).is_err());
    let mut tampered = honest.clone();
    tampered.entries[0].constant = f.addf(&c0, &f.one());
    assert!(verify(&tampered).is_err());
    // Definitions must match the layout and point into committed inputs.
    for source in [0, 4] {
        let mut bad = honest.clone();
        bad.entries[0].source = source;
        assert!(verify(&bad).is_err(), "source {source}");
    }
    assert!(verify(&VirtualInputs::none()).is_err());
    // A dishonest definition cannot be proven: the fragment output is nonzero.
    let mut rng = DeterministicRng::new(91);
    let (state, w) = p.prepare(vec![true, true, false], &mut rng).unwrap();
    let (mut joint, _, _) = param
        .commit(
            (w, ()),
            Transcript::for_test(b"virtual-inputs-test"),
            &mut rng,
        )
        .unwrap();
    assert!(prove(
        &mut joint.bound(&FrontendPart::new(&p, &[&main, &fragment], &[true]).unwrap()),
        state,
        &tampered,
        &ctx,
    )
    .is_err());
    // The primary circuit cannot read the virtual suffix.
    assert!(CircuitParticipant::new(&[&fragment, &main], 1, config, &ctx).is_err());
}

impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Every field, in declaration order. The pattern is exhaustive, so a new
    /// field does not compile until the statement tests cover it.
    #[allow(clippy::type_complexity)]
    pub(crate) fn fields_for_test(
        &self,
    ) -> (
        &CircuitGeometry,
        &PolygeroConfig,
        &Option<PolygeroParam>,
        &PackingCommitment<F>,
        &[u8; 32],
        &[[u8; 32]],
        &InputLayout,
        &Option<crate::runtime::v2::zk::storage::Split>,
    ) {
        let Self {
            geometry,
            config,
            param,
            backend,
            id,
            additional_ids,
            inputs,
            storage,
        } = self;
        (
            geometry,
            config,
            param,
            backend,
            id,
            additional_ids,
            inputs,
            storage,
        )
    }
}

impl<'a, const W: usize, F: ZkField<W> + PackingField> FrontendPart<'a, W, F> {
    /// Every field, in declaration order: the participant, the circuits and
    /// the public inputs. The pattern is exhaustive, so a new field does not
    /// compile until the statement tests cover it.
    pub(crate) fn fields_for_test(
        &self,
    ) -> (&'a CircuitParticipant<W, F>, &[&'a Circuit<F>], &[F::E]) {
        let Self {
            participant,
            circuits,
            public,
        } = self;
        (participant, circuits, public)
    }
}

/// A toy prime field registered under `FieldID::None`.
type UnregisteredPrime = FpGenericField<1, { LIMBS_PER_U64 }, { 4 * LIMBS_PER_U64 }, ()>;
impl Sealed for UnregisteredPrime {}
impl RegisteredField for UnregisteredPrime {
    const ID: FieldID = FieldID::None;
    const BYTES: usize = 8;
}

/// Participants are built only over registered fields, and only over the
/// field the registered ID names.
#[test]
fn participants_reject_unregistered_fields() {
    assert!(check_registered(&P256Field::new()).is_ok());
    assert!(check_registered(&Gf2_128Field::new()).is_ok());
    // FieldID::None is never registered.
    let toy = UnregisteredPrime::new_generic([0xffff_ffff_ffff_ffc5]);
    assert_eq!(
        check_registered(&toy).unwrap_err(),
        "v2 participant field is not registered"
    );
    // P-256's type over another prime (2^256 - 189) is not P-256.
    let other = P256Field::new_generic([0xffff_ffff_ffff_ff43, u64::MAX, u64::MAX, u64::MAX]);
    assert!(check_registered(&other).is_err());
}
