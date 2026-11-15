// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field,
            p256::P256Field,
            packing::PackingField,
            range_interpolation::{BinaryInterpolatorFactory, ScalarInterpolatorFactory},
        },
        random::{DeterministicRng, RandomEngine},
        v2::{
            polygero::{LinearStatement, PolygeroParam},
            proto::{
                polygero::{PolygeroCommitment, PolygeroConfig},
                witness_selection::{FingerprintResponse, FINGERPRINTS},
                Digest,
            },
            transcript::Transcript,
        },
    },
};

fn config() -> PolygeroConfig {
    PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    }
}
fn field<'a, const W: usize, F: RuntimeField<W> + PackingField, D: EvaluationDomain<W, F>>(
    n: usize,
    f: &'a F,
    d: &'a D,
) -> Field<'a, W, F, D> {
    Field::new(
        PolygeroParam::try_new(witness_count(n).unwrap(), config(), d).unwrap(),
        d,
        f.packing_id(),
    )
    .unwrap()
}

#[test]
fn response_codec_is_canonical_and_requires_both_coordinates() {
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    fn check<F: SerializableField>(f: &F, response: FingerprintResponse<F::E>) {
        let mut bytes = Vec::new();
        response.write(&mut bytes, f);
        let mut input = bytes.as_slice();
        assert_eq!(FingerprintResponse::read(&mut input, f).unwrap(), response);
        assert!(input.is_empty());
        for len in 0..bytes.len() {
            assert!(FingerprintResponse::read(&mut &bytes[..len], f).is_err());
        }
    }
    check(
        &f,
        FingerprintResponse {
            values: [f.zero(), f.one()],
        },
    );
    check(
        &p,
        FingerprintResponse {
            values: [p.zero(), p.mone()],
        },
    );
    assert!(FingerprintResponse::read(&mut &[255u8; 64][..], &p).is_err());
}

/// Test-only: this generic prime field has `FieldID::None`, so Elements of
/// it would not identify it; the test needs only its sampling.
impl crate::core::algebra::RegisteredField
    for crate::runtime::algebra::fp_generic::FpGenericField<
        1,
        { crate::runtime::algebra::limb::LIMBS_PER_U64 },
        { 3 * crate::runtime::algebra::limb::LIMBS_PER_U64 },
        (),
    >
{
}

#[test]
fn generic_sampling_and_three_fields_need_no_packing_capability() {
    use crate::runtime::algebra::{fp_generic::FpGenericField, limb::LIMBS_PER_U64};
    let small =
        FpGenericField::<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }, ()>::new_generic([17]);
    let sd = ScalarInterpolatorFactory::new(&small, 16);
    let small_param = PolygeroParam::try_new(
        witness_count(3).unwrap(),
        PolygeroConfig {
            k: 2,
            s: 1,
            n: 8,
            t: 1,
        },
        &sd,
    )
    .unwrap();
    let generic = Field::new(small_param, &sd, b"test/prime17/canonical".to_vec()).unwrap();
    let generic = Param::new((generic, ())).unwrap();
    let a = generic.challenges(&mut Transcript::for_test(b"generic-sampling").borrow());
    assert_eq!(a.0[0].len(), 3);

    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let param = Param::new((
        field(3, &f, &d),
        (field(2, &p, &pd), (field(0, &f, &d), ())),
    ))
    .unwrap();
    let mut rng = DeterministicRng::new(20);
    let witnesses = (
        rng.elt_field_slice(3, &f),
        (rng.elt_field_slice(2, &p), (vec![], ())),
    );
    let mut tp = Transcript::for_test(b"three-fields");
    let (prover, root, responses) = commit(&mut tp.bound(&param), witnesses, &mut rng).unwrap();
    let mut tv = Transcript::for_test(b"three-fields");
    let verifier = Verifier::receive(&mut tv.bound(&param), &root, responses);
    let proof = prover
        .prove_drawing(
            &mut tp.bound(&param),
            (statement(), (statement(), (statement(), ()))),
        )
        .unwrap();
    verifier
        .authenticate_drawing(
            &mut tv.bound(&param),
            &proof,
            (statement(), (statement(), (statement(), ()))),
        )
        .unwrap();
    assert_eq!(tp.u128(), tv.u128());
}

#[test]
fn frontend_cannot_address_fingerprint_masks_and_bad_lengths_do_not_consume_masks() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(3, &f, &d), ())).unwrap();
    let mut t = Transcript::for_test(b"shape");
    let mut rng = DeterministicRng::new(1);
    assert!(commit(&mut t.bound(&param), (vec![f.one(); 5], ()), &mut rng).is_err());
    assert_eq!(rng.bytes(32), DeterministicRng::new(1).bytes(32));
    let mut t = Transcript::for_test(b"shape");
    let a = param.challenges(&mut t.borrow());
    let mut s = statement();
    s.b.push(f.zero());
    s.a.push(PolygeroLinearTerm {
        c: 0,
        w: 3,
        k: f.one(),
    });
    let response = (
        FingerprintResponse {
            values: [f.zero(), f.zero()],
        },
        (),
    );
    assert!(param.fields.authenticate((s, ()), a, &response).is_err());
    assert!(witness_count(usize::MAX).is_err());
}
fn statement<E>() -> LinearStatement<E> {
    LinearStatement {
        a: vec![],
        b: vec![],
    }
}
fn residuals<const W: usize, F: RuntimeField<W>>(
    s: &LinearStatement<F::E>,
    witness: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut residuals = s.b.clone();
    for term in &s.a {
        f.fma(&mut residuals[term.c], &term.k, &witness[term.w]);
    }
    residuals
}

#[test]
fn both_characteristics_cover_every_cell_and_have_dedicated_masks() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let fields = (field(17, &f, &d), (field(13, &p, &pd), ()));
    let param = Param::new(fields.clone()).unwrap();
    let mut rng = DeterministicRng::new(17);
    let mut witnesses = (
        rng.elt_field_slice(17, &f),
        (rng.elt_field_slice(13, &p), ()),
    );
    fields.append_masks(&mut witnesses, &mut rng);
    let a = param.challenges(&mut Transcript::for_test(b"cell-coverage").borrow());
    assert_ne!(a.0[0], a.0[1]);
    assert_ne!(a.1 .0[0], a.1 .0[1]);
    let responses = fields.responses(&witnesses, &a);
    let s = fields
        .authenticate((statement(), (statement(), ())), a, &responses)
        .unwrap();
    fn check<const W: usize, F: RuntimeField<W>>(
        s: &LinearStatement<F::E>,
        w: &[F::E],
        n: usize,
        f: &F,
    ) {
        assert!(residuals(s, w, f).iter().all(|x| f.is_zero(x)));
        for i in 0..n {
            let mut bad = w.to_vec();
            f.add(&mut bad[i], &f.one());
            assert!(
                residuals(s, &bad, f).iter().any(|x| !f.is_zero(x)),
                "original cell {i}"
            );
        }
        for j in 0..FINGERPRINTS {
            let terms: Vec<_> =
                s.a.iter()
                    .filter(|term| term.c == j && term.w >= n)
                    .collect();
            assert_eq!(terms.len(), 1);
            assert_eq!(terms[0].w, n + j);
            let mut bad = w.to_vec();
            f.add(&mut bad[n + j], &f.one());
            let errors = residuals(s, &bad, f);
            assert!(!f.is_zero(&errors[j]));
            assert!(f.is_zero(&errors[1 - j]));
        }
    }
    check(&s.0, &witnesses.0, 17, &f);
    check(&s.1 .0, &witnesses.1 .0, 13, &p);
}

#[test]
fn joint_roundtrip_and_each_forged_response_are_checked_by_backend() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let param = Param::new((field(17, &f, &d), (field(13, &p, &pd), ()))).unwrap();
    for forged in 0..5 {
        let mut rng = DeterministicRng::new(19);
        let witnesses = (
            rng.elt_field_slice(17, &f),
            (rng.elt_field_slice(13, &p), ()),
        );
        let mut tp = Transcript::for_test(b"selection/backend");
        let (mut prover, root, mut responses) =
            commit(&mut tp.bound(&param), witnesses, &mut rng).unwrap();
        let mut tv = Transcript::for_test(b"selection/backend");
        if forged > 0 {
            // Rebind the forged response on BOTH sides. Arithmetic rejection is
            // required even when the transcript prefix and final seal agree.
            if forged <= 2 {
                f.add(&mut responses.0.values[forged - 1], &f.one());
            } else {
                p.add(&mut responses.1 .0.values[forged - 3], &p.one());
            }
        }
        let verifier = Verifier::receive(&mut tv.bound(&param), &root, responses.clone());
        if forged == 0 {
            assert_eq!(tp.u128(), tv.u128());
            // Sampling this extra common round is deliberate and symmetric.
        } else {
            // Retain the original committed oracle but authenticate a false row,
            // on a copy of the verifier's session.
            tp = tv.fork_for_test();
            let b = tp.bound(&param);
            prover.backend.adopt_session_for_test(&b);
            prover.session = b.session();
        }
        let prover = Prover {
            responses,
            ..prover
        };
        let proof = prover
            .prove_drawing(&mut tp.bound(&param), (statement(), (statement(), ())))
            .unwrap();
        let result = verifier.authenticate_drawing(
            &mut tv.bound(&param),
            &proof,
            (statement(), (statement(), ())),
        );
        assert_eq!(result.is_ok(), forged == 0);
        if forged == 0 {
            assert_eq!(tp.u128(), tv.u128());
        }
    }
}

#[test]
fn coefficients_follow_the_commitment_and_read_one_stream() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(17, &f, &d), ())).unwrap();
    let root = PolygeroCommitment {
        root: Digest { data: [7; 32] },
    };
    let other = PolygeroCommitment {
        root: Digest { data: [8; 32] },
    };
    let responses = (
        FingerprintResponse {
            values: [f.zero(), f.one()],
        },
        (),
    );
    let mut actual = Transcript::for_test(b"selection/root-binding");
    let _verifier = Verifier::receive(&mut actual.bound(&param), &root, responses.clone());
    // The statement fixes every layout; the coefficients are drawn from the
    // boundary after the `Commitment` message (Bytes(32), the encoding of a
    // test message), both vectors from one stream.
    let coefficients = |root: &PolygeroCommitment| {
        let mut t = Transcript::for_test(b"selection/root-binding");
        t.send_for_test(&root.root.data);
        let mut fork = t.fork_for_test();
        let drawn = param.challenges(&mut t.borrow());
        let raw = fork.borrow().draw(|r| r.bytes(2 * 17 * 16));
        let expected: Vec<_> = raw
            .as_chunks::<16>()
            .0
            .iter()
            .map(|x| f.bytes_to_element(x).unwrap())
            .collect();
        assert_eq!(drawn.0[0], expected[..17]);
        assert_eq!(drawn.0[1], expected[17..]);
        (drawn, t)
    };
    let (a, mut expected) = coefficients(&root);
    assert_ne!(a.0, coefficients(&other).0 .0);
    param.send_responses(&responses, &mut expected.borrow());
    assert_eq!(actual.round_count_for_test(), 1);
    assert_eq!(actual.bytes(32), expected.bytes(32));
}

/// distinct fingerprint responses must change every later challenge.
#[test]
fn fingerprint_responses_are_bound_before_later_challenges() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(17, &f, &d), ())).unwrap();
    let root = PolygeroCommitment {
        root: Digest { data: [7; 32] },
    };
    let state = |values| {
        let responses = (FingerprintResponse { values }, ());
        let mut t = Transcript::for_test(b"selection/response-binding");
        let _verifier = Verifier::receive(&mut t.bound(&param), &root, responses);
        t.bytes(32)
    };
    assert_ne!(state([f.zero(), f.one()]), state([f.one(), f.one()]));
    assert_ne!(state([f.zero(), f.one()]), state([f.zero(), f.zero()]));
}

#[test]
fn prover_and_verifier_states_complete_only_on_their_own_session() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(3, &f, &d), ())).unwrap();
    let commit_on = |t: &mut Transcript| {
        let mut rng = DeterministicRng::new(5);
        let witnesses = (rng.elt_field_slice(3, &f), ());
        commit(&mut t.bound(&param), witnesses, &mut rng).unwrap()
    };
    // Forks hold the same bytes but are other sessions.
    let mut stale = Transcript::for_test(b"selection/session");
    let (stale_prover, _, _) = commit_on(&mut stale);
    let mut stale_fork = stale.fork_for_test();
    assert_eq!(
        stale_prover
            .prove_drawing(&mut stale_fork.bound(&param), (statement(), ()))
            .unwrap_err(),
        "witness selection session mismatch"
    );
    let mut tp = Transcript::for_test(b"selection/session");
    let (prover, root, responses) = commit_on(&mut tp);
    let proof = prover
        .prove_drawing(&mut tp.bound(&param), (statement(), ()))
        .unwrap();
    let mut tv = Transcript::for_test(b"selection/session");
    let verifier = Verifier::receive(&mut tv.bound(&param), &root, responses);
    let mut tv_fork = tv.fork_for_test();
    assert_eq!(
        verifier
            .authenticate_drawing(&mut tv_fork.bound(&param), &proof, (statement(), ()))
            .err()
            .unwrap(),
        "witness selection session mismatch"
    );
}

/// Draw the batching weights right before the response phase, as a caller
/// that holds its complete statements does.
impl<S, C, R> Prover<S, C, R> {
    pub(crate) fn prove_drawing<L: Fields<Coefficients = C, Responses = R>>(
        self,
        t: &mut Bound<'_, Param<L>>,
        statements: Statements<L>,
    ) -> Result<JointPolygeroProof<Bodies<L>>, String>
    where
        L::Backend: BackendParticipants<States = S>,
    {
        let batch = Param::weights(t, &statements);
        self.prove(t, batch, statements)
    }
}
impl<L: Fields> Verifier<L> {
    pub(crate) fn authenticate_drawing(
        self,
        t: &mut Bound<'_, Param<L>>,
        proof: &JointPolygeroProof<Bodies<L>>,
        statements: Statements<L>,
    ) -> Result<Authenticated, String> {
        let batch = Param::weights(t, &statements);
        self.authenticate(t, batch, proof, statements)
    }
}
