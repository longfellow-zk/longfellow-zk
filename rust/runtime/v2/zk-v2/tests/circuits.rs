// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField, SupportsU64Conversions},
        proto::v2::{self, Layer, Linear, Quadratic, RawCircuit, Stream},
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory, RuntimeField,
        },
        random::{transcript_v2::Transcript, DeterministicRng},
    },
};

#[test]
fn selected_joint_wrapper_supports_three_typed_fields() {
    use crate::runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, PackingField},
        polygero::{LinearStatement, PolygeroConfig},
        proto::Digest,
        random::transcript_v2::Transcript,
        zk_v2::joint::{JointParam, SelectedField},
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
    let a = SelectedField::new(2, config, &f, &d, f.packing_id()).unwrap();
    assert_eq!(a.geometry().nw, 4);
    let param = JointParam::new((
        a,
        (
            SelectedField::new(1, config, &p, &pd, p.packing_id()).unwrap(),
            (
                SelectedField::new(0, config, &f, &d, f.packing_id()).unwrap(),
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
    let mut tp = Transcript::new(b"zk-v2/selected-three-fields");
    let (prover, root, responses) = param
        .commit(
            (vec![f.one(), f.zero()], (vec![p.one()], (vec![], ()))),
            &mut tp,
            &mut DeterministicRng::new(91),
        )
        .unwrap();
    let proof = prover.prove(&param, statements(), &mut tp).unwrap();
    let verify = |responses| {
        let mut tv = Transcript::new(b"zk-v2/selected-three-fields");
        param
            .clone()
            .receive(&root, responses, &mut tv)
            .unwrap()
            .authenticate(&proof, statements(), &mut tv)
    };
    verify(responses.clone()).unwrap();
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
        let raw = RawCircuit {
            ninput: 4,
            npublic_input: 1,
            noutput: 1,
            logv: 0,
            constants: vec![f.zero(), f.one(), f.mone()],
            layers,
        };
        Circuit {
            id: v2::compute_id(f, &raw),
            raw,
        }
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
fn binary_circuits_authenticate_one_shared_input() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
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
            crate::runtime::zk_v2::joint::JointParam::new((p.participant(&ctx).unwrap(), ()))
                .unwrap();
        let mut t = Transcript::new(b"fragmented-pcs-test");
        p.bind(&mut t);
        let (joint, root, responses) = param.commit((w, ()), &mut t, &mut rng).unwrap();
        let (proof, statement) = p
            .prove_circuits(&main, &[true], private, state, &others, &mut t, &ctx)
            .unwrap();
        let opening = joint.prove(&param, (statement, ()), &mut t).unwrap();
        let verify = |candidate: &CircuitProof<2, Gf2_128Field>, public: bool| {
            let mut t = Transcript::new(b"fragmented-pcs-test");
            p.bind(&mut t);
            let v = param
                .clone()
                .receive(&root, responses.clone(), &mut t)
                .unwrap();
            let statement =
                p.verify_circuits(&main, &[public], candidate, &others, &mut t, &ctx)?;
            v.authenticate(&opening, (statement, ()), &mut t)
                .map(|_| ())
                .map_err(|e| e.to_string())
        };
        verify(&proof, true).unwrap();
        assert!(verify(&proof, false).is_err());
        let mut changed = proof.clone();
        f.add(&mut changed.sumcheck_proof.layers[0].claims[1], &f.one());
        assert!(verify(&changed, true).is_err());
        if count > 0 {
            let (_, mut wrong) = circuits(&f);
            wrong.raw.ninput += 1;
            let invalid = vec![&wrong; count];
            let mut t = Transcript::new(b"bad-shared-layout");
            let before = t.fork_for_test().bytes(32);
            assert!(p
                .verify_circuits(&main, &[true], &proof, &invalid, &mut t, &ctx)
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
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
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
        crate::runtime::zk_v2::joint::JointParam::new((p.participant(&ctx).unwrap(), ())).unwrap();
    let mut t = Transcript::new(b"prime-fragmented-pcs-test");
    p.bind(&mut t);
    let (joint, root, responses) = param.commit((w, ()), &mut t, &mut rng).unwrap();
    let (proof, statement) = p
        .prove_circuits(&main, &public, private, state, &others, &mut t, &ctx)
        .unwrap();
    assert!(matches!(
        proof.packing,
        crate::runtime::proto::dual_packing::PackingProof::Direct
    ));
    let opening = joint.prove(&param, (statement, ()), &mut t).unwrap();
    let mut t = Transcript::new(b"prime-fragmented-pcs-test");
    p.bind(&mut t);
    let v = param.receive(&root, responses, &mut t).unwrap();
    let statement = p
        .verify_circuits(&main, &public, &proof, &others, &mut t, &ctx)
        .unwrap();
    v.authenticate(&opening, (statement, ()), &mut t)
        .map(|_| ())
        .unwrap();
}
