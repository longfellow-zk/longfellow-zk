// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField, SupportsU64Conversions},
        proto::v2::{self, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory, RuntimeField,
        },
        random::DeterministicRng,
        v2::transcript::Transcript,
    },
};

#[test]
fn selected_joint_wrapper_supports_three_typed_fields() {
    use crate::runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, PackingField},
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            proto::Digest,
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
    let a = SelectedField::new(2, config, &d, f.packing_id()).unwrap();
    assert_eq!(a.geometry().nw, 4);
    let param = JointParam::new((
        a,
        (
            SelectedField::new(1, config, &pd, p.packing_id()).unwrap(),
            (
                SelectedField::new(0, config, &d, f.packing_id()).unwrap(),
                (),
            ),
        ),
    ))
    .unwrap();
    let statements = || {
        (
            LinearStatement {
                a: vec![],
                b: vec![],
                digest: Digest { data: [1; 32] },
            },
            (
                LinearStatement {
                    a: vec![],
                    b: vec![],
                    digest: Digest { data: [2; 32] },
                },
                (
                    LinearStatement {
                        a: vec![],
                        b: vec![],
                        digest: Digest { data: [3; 32] },
                    },
                    (),
                ),
            ),
        )
    };
    let tp = Transcript::new(b"zk-v2/selected-three-fields");
    let (prover, root, responses) = param
        .commit(
            (vec![f.one(), f.zero()], (vec![p.one()], (vec![], ()))),
            tp,
            &mut DeterministicRng::new(91),
        )
        .unwrap();
    let (proof, mut tp) = prover.prove(&param, statements()).unwrap();
    let verify = |responses| {
        let tv = Transcript::new(b"zk-v2/selected-three-fields");
        param
            .clone()
            .receive(&root, responses, tv)
            .authenticate(&proof, statements())
    };
    let mut tv = verify(responses.clone()).unwrap().into_transcript();
    assert_eq!(tp.bytes(32), tv.bytes(32));
    let mut altered = responses;
    f.add(&mut altered.1 .1 .0.values[1], &f.one());
    assert!(verify(altered).is_err());
}
fn circuits<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
) -> (Circuit<F>, Circuit<F>) {
    let layer = |nw, q, l| {
        Layer::with_assertions(
            nw,
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::default(),
            |k| k == 0,
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
        Circuit::new(v2::compute_id(f, &raw), raw)
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
#[test]
fn prime_frontend_uses_widths_instead_of_cached_logw() {
    use crate::runtime::{
        algebra::{blas, p256::P256Field},
        v2::{sumcheck, zk::prime},
    };
    let f = P256Field::new();
    for cached_logw in [0, 2, 41] {
        let (circuit, _) = circuits(&f);
        let mut raw = circuit.into_raw().into_builder();
        raw.layers[0].logw = cached_logw;
        let raw = raw.build();
        let circuit = Circuit::new(v2::compute_id(&f, &raw), raw);
        let geometry = sumcheck::circuit_geometry(&[&circuit]).unwrap();
        assert_eq!(geometry.logw_layers, [2]);
        // The fixture asserts x*y = public and its last private input = 0.
        let public = [f.u64_to_element(6)];
        let private = vec![f.u64_to_element(2), f.u64_to_element(3), f.zero()];
        let state = prime::prepare(&circuit, private, &mut DeterministicRng::new(42), &f).unwrap();
        assert_eq!(state.values.len(), 3 + geometry.pad_count().unwrap());
        let witness = state.values.clone();
        let mut tp = Transcript::new(b"prime-width-geometry");
        let mut tv = tp.fork_for_test();
        let (proof, claim) = prime::prove(&circuit, &public, state, &mut tp.borrow(), &f).unwrap();
        let checked = prime::reduce(&circuit, &public, &proof, &mut tv.borrow(), &f).unwrap();
        assert_eq!(claim.weights, checked.weights);
        assert_eq!(claim.target, checked.target);
        assert_eq!(blas::dot(&claim.weights, &witness, &f), claim.target);
        assert_eq!(tp.bytes(32), tv.bytes(32));
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
        let others = vec![&side; count];
        let p = CircuitParticipant::with_circuits(&main, &others, config, &ctx).unwrap();
        let private = vec![true, true, false];
        let mut rng = DeterministicRng::new(77);
        let (state, w) = p.prepare(&private, &mut rng).unwrap();
        // Circuit multiplicity changes pads, but never duplicates the packed input.
        assert_eq!(p.backend.layout.private_inputs, 3);
        let param =
            crate::runtime::v2::zk::joint::JointParam::new((p.participant(&ctx).unwrap(), ()))
                .unwrap();
        let mut t = Transcript::new(b"fragmented-pcs-test");
        p.bind(&mut t.borrow());
        let (mut joint, root, responses) = param.commit((w, ()), t, &mut rng).unwrap();
        let (proof, statement) = p
            .prove_circuits(
                &main,
                &[true],
                private,
                state,
                &others,
                &mut joint.transcript(),
                &ctx,
            )
            .unwrap();
        let (opening, _) = joint.prove(&param, (statement, ())).unwrap();
        let verify = |candidate: &CircuitProof<2, Gf2_128Field>, public: bool| {
            let mut t = Transcript::new(b"fragmented-pcs-test");
            p.bind(&mut t.borrow());
            let mut v = param.clone().receive(&root, responses.clone(), t);
            let statement = p.reduce_circuits(
                &main,
                &[public],
                candidate,
                &others,
                &mut v.transcript(),
                &ctx,
            )?;
            v.authenticate(&opening, (statement, ()))
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
            let wrong = Circuit::new(id, raw.build());
            let invalid = vec![&wrong; count];
            let mut t = Transcript::new(b"bad-shared-layout");
            let before = t.fork_for_test().bytes(32);
            assert!(p
                .reduce_circuits(&main, &[true], &proof, &invalid, &mut t.borrow(), &ctx)
                .is_err());
            assert_eq!(before, t.bytes(32));
            assert!(CircuitParticipant::with_circuits(&main, &invalid, config, &ctx).is_err());
        }
    }
}
#[test]
fn prime_circuits_keep_degree_one_packing_direct() {
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
    let others = [&side, &main];
    let p = CircuitParticipant::with_circuits(
        &main,
        &others,
        PolygeroConfig {
            k: 64,
            s: 2,
            n: 256,
            t: 8,
        },
        &ctx,
    )
    .unwrap();
    let private = [2, 3, 0].map(|x| f.u64_to_element(x)).to_vec();
    let public = [f.u64_to_element(6)];
    let mut rng = DeterministicRng::new(78);
    let (state, w) = p.prepare(&private, &mut rng).unwrap();
    assert_eq!(p.geometry().packing_degree, 1);
    assert_eq!(
        w.len(),
        private.len() + p.geometry().sc_geom.pad_count().unwrap()
    );
    let param =
        crate::runtime::v2::zk::joint::JointParam::new((p.participant(&ctx).unwrap(), ())).unwrap();
    let mut t = Transcript::new(b"prime-fragmented-pcs-test");
    p.bind(&mut t.borrow());
    let (mut joint, root, responses) = param.commit((w, ()), t, &mut rng).unwrap();
    let (proof, statement) = p
        .prove_circuits(
            &main,
            &public,
            private,
            state,
            &others,
            &mut joint.transcript(),
            &ctx,
        )
        .unwrap();
    assert!(matches!(
        proof.packing,
        crate::runtime::v2::proto::dual_packing::PackingProof::Direct
    ));
    let (opening, mut tp) = joint.prove(&param, (statement, ())).unwrap();
    let mut t = Transcript::new(b"prime-fragmented-pcs-test");
    p.bind(&mut t.borrow());
    let mut v = param.receive(&root, responses, t);
    let statement = p
        .reduce_circuits(&main, &public, &proof, &others, &mut v.transcript(), &ctx)
        .unwrap();
    let mut tv = v
        .authenticate(&opening, (statement, ()))
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
    let circuit = v2::Circuit::new([0; 32], raw);
    let prover = crate::runtime::v2::zk::ZkProver::new(
        circuit,
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
    );
    let mut rng = DeterministicRng::new(42);
    let result = prover.commit(
        &[],
        &ZkContext::new(&domain),
        Transcript::new(b"invalid metadata"),
        &mut rng,
    );
    assert!(matches!(result, Err(ref e) if e == "public prefix"));
    assert_eq!(rng.state, 42);
}

#[test]
fn final_seal_failure_has_its_own_verification_error() {
    use crate::runtime::v2::zk::{ZkProof, ZkProver, ZkVerificationError, ZkVerifier};
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
    let prover = ZkProver::new(circuit, config);
    let private = vec![false; 3];
    let (committed, geometry) = prover
        .commit(
            &private,
            &context,
            Transcript::new(b"seal error"),
            &mut DeterministicRng::new(45),
        )
        .unwrap();
    let (proof, transcript) = prover
        .prove(&[false], private, committed, &context)
        .unwrap();
    let mut bytes = proof.write(&geometry, &f, transcript).unwrap().into_bytes();
    let verifier = ZkVerifier::new(prover.circuit, config, &context).unwrap();
    let mut input = bytes.as_slice();
    let decoded = ZkProof::read(&mut input, &geometry, &f).unwrap();
    verifier
        .verify(&[false], decoded, Transcript::new(b"seal error"), &context)
        .unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    let mut changed = bytes.as_slice();
    let tampered = ZkProof::read(&mut changed, &geometry, &f).unwrap();
    assert!(matches!(
        verifier.verify(&[false], tampered, Transcript::new(b"seal error"), &context),
        Err(ZkVerificationError::InvalidTranscriptSeal(_))
    ));
}
