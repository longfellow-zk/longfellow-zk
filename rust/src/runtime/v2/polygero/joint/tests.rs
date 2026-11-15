// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{AlgebraicField, RegisteredField},
    runtime::{
        algebra::{
            blas,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{BinaryInterpolatorFactory, ScalarInterpolatorFactory},
        },
        random::{DeterministicRng, RandomEngine},
        v2::{
            polygero::{
                prover_commitment::ColumnOracle, JointPolygeroProver, JointPolygeroVerifier,
            },
            proto::polygero::PolygeroCommitment,
            transcript::Bound,
        },
    },
};

impl<S> JointPolygeroProver<S> {
    // Deliberately forged proofs need a matching session to exercise the
    // arithmetic checks rather than failing only at commitment authentication.
    pub(crate) fn adopt_session_for_test<P>(&mut self, t: &Bound<'_, P>) {
        self.session = t.session();
    }
}

fn config() -> PolygeroConfig {
    PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    }
}
fn field<
    'a,
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    f: &'a F,
    d: &'a D,
    n: usize,
    c: PolygeroConfig,
) -> (Participant<'a, W, F, D>, Vec<F::E>, LinearStatement<F::E>) {
    let mut rng = DeterministicRng::new(n as u64 + 1);
    let w = rng.elt_field_slice(n, f);
    let p = Participant::new(PolygeroParam::try_new(n, c, d).unwrap(), d).unwrap();
    let a = w
        .iter()
        .enumerate()
        .map(|(i, _)| PolygeroLinearTerm {
            c: 0,
            w: i,
            k: f.one(),
        })
        .collect();
    let b = vec![f.neg(&blas::dot1(&w, f))];
    (p, w, LinearStatement { a, b })
}
fn roundtrip<L: Participants + Clone>(p: JointPolygeroParam<L>, w: L::Witnesses, s: L::Statements) {
    let mut tp = Transcript::for_test(b"joint/test");
    let mut tv = tp.fork_for_test();
    let (prover, root) =
        JointPolygeroProver::commit(&mut tp.bound(&p), w, &mut DeterministicRng::new(7)).unwrap();
    assert_eq!(tp.round_count_for_test(), 0);
    let proof = prover.prove_drawing(&mut tp.bound(&p), &s).unwrap();
    // All participants share one batching round and one opening round.
    assert_eq!(tp.round_count_for_test(), 2);
    let bytes = p.write(&proof, tp.fork_for_test()).unwrap().into_bytes();
    let mut input = bytes.as_slice();
    let decoded = p.read(&mut input).unwrap();
    assert!(input.is_empty());
    assert_eq!(
        p.write(&decoded, tp.fork_for_test()).unwrap().into_bytes(),
        bytes
    );
    let verifier = JointPolygeroVerifier::receive(&mut tv.bound(&p), &root);
    assert_eq!(tv.round_count_for_test(), 0);
    verifier
        .reduce_drawing(&mut tv.bound(&p), &decoded, &s)
        .unwrap();
    assert_eq!(tv.round_count_for_test(), 2);
    assert_eq!(tp.u128(), tv.u128());
    let decoded = p.read(&mut bytes.as_slice()).unwrap();
    let mut tf = Transcript::for_test(b"joint/test");
    let full = JointPolygeroVerifier::receive(&mut tf.bound(&p), &root);
    full.verify_drawing(tf, &p, decoded, &s).unwrap();
    // Only a cut of whole frontier digests passes the length check.
    for len in 0..bytes.len() {
        assert!(
            p.read(&mut &bytes[..len]).is_err() || (bytes.len() - len).is_multiple_of(32),
            "prefix {len}"
        );
    }
}
#[test]
fn recursive_one_two_three_and_repeated_fields() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let (c, wc, sc) = field(&p, &pd, 0, config());
    roundtrip(
        JointPolygeroParam::new((a.clone(), ())).unwrap(),
        (wa.clone(), ()),
        (sa.clone(), ()),
    );
    roundtrip(
        JointPolygeroParam::new((a.clone(), (b.clone(), ()))).unwrap(),
        (wa.clone(), (wb.clone(), ())),
        (sa.clone(), (sb.clone(), ())),
    );
    roundtrip(
        JointPolygeroParam::new((a.clone(), (b, (c, ())))).unwrap(),
        (wa.clone(), (wb, (wc, ()))),
        (sa.clone(), (sb, (sc, ()))),
    );
    roundtrip(
        JointPolygeroParam::new((a.clone(), (a, ()))).unwrap(),
        (wa.clone(), (wa, ())),
        (sa.clone(), (sa, ())),
    );
}
#[test]
fn joint_authenticates_every_field_response_column_and_opening() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let param = JointPolygeroParam::new((a, (b, ()))).unwrap();
    let s = (sa, (sb, ()));
    let mut t = Transcript::for_test(b"joint/tamper");
    let (prover, root) = JointPolygeroProver::commit(
        &mut t.bound(&param),
        (wa, (wb, ())),
        &mut DeterministicRng::new(9),
    )
    .unwrap();
    let proof = prover.prove_drawing(&mut t.bound(&param), &s).unwrap();
    let verify = |candidate: &JointPolygeroProof<_>, statements: &_| {
        let mut tv = Transcript::for_test(b"joint/tamper");
        let v = JointPolygeroVerifier::receive(&mut tv.bound(&param), &root);
        v.reduce_drawing(&mut tv.bound(&param), candidate, statements)
    };
    verify(&proof, &s).unwrap();
    for part in 0..2 {
        for component in 0..3 {
            let len = if part == 0 {
                [
                    proof.bodies.0.h.len(),
                    proof.bodies.0.z.len(),
                    proof.bodies.0.rows.len(),
                ][component]
            } else {
                [
                    proof.bodies.1 .0.h.len(),
                    proof.bodies.1 .0.z.len(),
                    proof.bodies.1 .0.rows.len(),
                ][component]
            };
            for i in 0..len {
                let mut bad = proof.clone();
                if part == 0 {
                    let values = match component {
                        0 => &mut bad.bodies.0.h,
                        1 => &mut bad.bodies.0.z,
                        _ => &mut bad.bodies.0.rows,
                    };
                    f.add(&mut values[i], &f.one());
                } else {
                    let values = match component {
                        0 => &mut bad.bodies.1 .0.h,
                        1 => &mut bad.bodies.1 .0.z,
                        _ => &mut bad.bodies.1 .0.rows,
                    };
                    p.add(&mut values[i], &p.one());
                }
                assert!(verify(&bad, &s).is_err());
            }
        }
    }
    for i in 0..proof.opening.nonce.len() {
        let mut bad = proof.clone();
        bad.opening.nonce[i].bytes[0] ^= 1;
        assert!(verify(&bad, &s).is_err());
    }
    for i in 0..proof.opening.path.len() {
        let mut bad = proof.clone();
        bad.opening.path[i].data[0] ^= 1;
        assert!(verify(&bad, &s).is_err());
    }
    let mut bad = s.clone();
    p.add(&mut bad.1 .0.b[0], &p.one());
    assert!(verify(&proof, &bad).is_err());
    let mut bad = proof.clone();
    bad.bodies.1 .0.rows.pop();
    assert!(verify(&bad, &s).is_err());
    let original = param.queries(
        &proof.bodies,
        &mut Transcript::for_test(b"queries").borrow(),
    );
    let mut changed = false;
    for i in 0..16 {
        let mut bad = proof.clone();
        p.add(&mut bad.bodies.1 .0.z[i], &p.one());
        changed |=
            param.queries(&bad.bodies, &mut Transcript::for_test(b"queries").borrow()) != original;
    }
    assert!(changed);
    let mut wrong = Transcript::for_test(b"wrong-session");
    let v = JointPolygeroVerifier::receive(&mut wrong.bound(&param), &root);
    assert!(v
        .reduce_drawing(&mut wrong.bound(&param), &proof, &s)
        .is_err());
    let mut other = root.clone();
    other.root.data[0] ^= 1;
    let mut tv = Transcript::for_test(b"joint/tamper");
    let v = JointPolygeroVerifier::receive(&mut tv.bound(&param), &other);
    assert!(v.reduce_drawing(&mut tv.bound(&param), &proof, &s).is_err());
}
#[test]
fn invalid_lists_witnesses_and_statements_do_not_sample() {
    assert!(JointPolygeroParam::new(()).is_err());
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 256);
    let (a, w, s) = field(&f, &d, 5, config());
    let (b, _, _) = field(&f, &d, 5, PolygeroConfig { k: 9, ..config() });
    assert!(JointPolygeroParam::new((a.clone(), (b, ()))).is_err());
    let param = JointPolygeroParam::new((a, ())).unwrap();
    let mut t = Transcript::for_test(b"invalid");
    let mut rng = DeterministicRng::new(4);
    let mut before_rng = rng.clone();
    let mut bad = w.clone();
    bad.pop();
    assert!(JointPolygeroProver::commit(&mut t.bound(&param), (bad, ()), &mut rng).is_err());
    assert_eq!(rng.bytes(32), before_rng.bytes(32));
    let mut valid = Transcript::for_test(b"invalid");
    let (prover, _) =
        JointPolygeroProver::commit(&mut valid.bound(&param), (w, ()), &mut rng).unwrap();
    let mut bad = s;
    bad.a[0].w = usize::MAX;
    assert!(prover
        .prove_drawing(&mut valid.bound(&param), &(bad, ()))
        .is_err());
}

#[test]
fn forged_linear_witness_is_rejected_even_with_a_genuine_opening() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let (a, w, s) = field(&f, &d, 5, config());
    let param = JointPolygeroParam::new((a, ())).unwrap();
    let mut t = Transcript::for_test(b"virtual");
    let (mut prover, _) = JointPolygeroProver::commit(
        &mut t.bound(&param),
        (w, ()),
        &mut DeterministicRng::new(11),
    )
    .unwrap();
    let g = param.participants.0.param.geom;
    let z = 2; // First ordinary data row; every row is sent and authenticated.
    for x in &mut prover.states.0[z] {
        f.add(x, &f.one());
    }
    prover.oracle = ColumnOracle::new(g.n, &mut DeterministicRng::new(12), |j, h| {
        param.participants.append_encoded(&prover.states, j, h)
    });
    let root = PolygeroCommitment {
        root: prover.oracle.root(),
    };
    let mut forged = Transcript::for_test(b"virtual");
    param.receive(&root, &mut forged.borrow());
    prover.adopt_session_for_test(&forged.bound(&param));
    let proof = prover
        .prove_drawing(&mut forged.bound(&param), &(s.clone(), ()))
        .unwrap();
    let mut tv = Transcript::for_test(b"virtual");
    let v = JointPolygeroVerifier::receive(&mut tv.bound(&param), &root);
    let error = v
        .reduce_drawing(&mut tv.bound(&param), &proof, &(s, ()))
        .err()
        .unwrap();
    assert_eq!(error.0, "Polygero global arithmetic sum failed");
}

#[test]
fn tuple_codec_rejects_noncanonical_field_bytes_and_bad_lengths() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let param = JointPolygeroParam::new((a, (b, ()))).unwrap();
    let mut t = Transcript::for_test(b"codec");
    let (prover, _) = JointPolygeroProver::commit(
        &mut t.bound(&param),
        (wa, (wb, ())),
        &mut DeterministicRng::new(2),
    )
    .unwrap();
    let proof = prover
        .prove_drawing(&mut t.bound(&param), &(sa, (sb, ())))
        .unwrap();
    let bytes = param.write(&proof, t.fork_for_test()).unwrap().into_bytes();
    // The body is the binary response, then the prime response, with no
    // magic.
    let mut bad = bytes.clone();
    let first_prime = (proof.bodies.0.h.len() + proof.bodies.0.z.len()) * 16;
    bad[first_prime..first_prime + 32].fill(255);
    assert!(param.read(&mut bad.as_slice()).is_err());
    let mut bad = bytes.clone();
    let n = bad.len();
    bad[n - 4..].fill(255);
    // The seal block may hold any bytes at parse time.
    assert!(param.read(&mut bad.as_slice()).is_ok());
    // The frontier carries its count: no extension parses, not even whole
    // digests.
    for extra in [1, 31, 32, 33] {
        let mut bad = bytes.clone();
        bad.splice(n - 32..n - 32, vec![0; extra]);
        assert!(
            param.read(&mut bad.as_slice()).is_err(),
            "{extra} extra bytes"
        );
    }
    // With the count adjusted, one more or one fewer digest parses.
    let count = proof.opening.path.len();
    assert!(count > 0);
    let at = n - 32 - 32 * count - 8;
    let recount = |edited: &mut Vec<u8>, digests: usize| {
        edited[at..at + 8].copy_from_slice(&(digests as u64).to_le_bytes())
    };
    let mut longer = bytes.clone();
    longer.splice(n - 32..n - 32, vec![0; 32]);
    assert!(param.read(&mut longer.as_slice()).is_err());
    recount(&mut longer, count + 1);
    assert!(param.read(&mut longer.as_slice()).is_ok());
    let mut shorter = bytes;
    shorter.drain(n - 64..n - 32);
    assert!(param.read(&mut shorter.as_slice()).is_err());
    recount(&mut shorter, count - 1);
    assert!(param.read(&mut shorter.as_slice()).is_ok());
}
#[test]
fn ordinary_rows_support_large_mask_prefixes_and_partial_words() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    for (n, k, t) in [(0, 8, 6), (1, 3, 2), (7, 8, 6)] {
        let (a, w, s) = field(&f, &d, n, PolygeroConfig { k, t, ..config() });
        roundtrip(JointPolygeroParam::new((a, ())).unwrap(), (w, ()), (s, ()));
    }
}

#[test]
fn batching_follows_the_absorbed_messages_and_precedes_the_responses() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let param = JointPolygeroParam::new((a, (b, ()))).unwrap();
    let s = (sa, (sb, ()));
    let mut tp = Transcript::for_test(b"joint/order");
    let (prover, _root) = JointPolygeroProver::commit(
        &mut tp.bound(&param),
        (wa, (wb, ())),
        &mut DeterministicRng::new(98),
    )
    .unwrap();
    let mut manual = tp.fork_for_test();
    let first = param.challenges(&s, &mut manual.borrow()).0;
    // Statements are never absorbed (transcript I3): the batching challenges
    // depend only on the messages absorbed before them, so changing the last
    // statement's targets leaves the first participant's weights unchanged.
    // Frontends derive their statements from those messages; a static system
    // (tests and tools only) is not bound.
    let mut changed = s.clone();
    p.add(&mut changed.1 .0.b[0], &p.one());
    let mut changed_ts = tp.fork_for_test();
    let changed_challenges = param.challenges(&changed, &mut changed_ts.borrow());
    assert_eq!(first.alpha, changed_challenges.0.alpha);
    let proof = prover.prove_drawing(&mut tp.bound(&param), &s).unwrap();
    let _indices = param.queries(&proof.bodies, &mut manual.borrow());
    assert_eq!(manual.bytes(32), tp.bytes(32));
}

#[test]
fn participant_order_and_late_errors_are_bound_before_sampling() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let (a, wa, sa) = field(&f, &d, 7, config());
    let (b, wb, sb) = field(&f, &d, 5, config());
    let forward = JointPolygeroParam::new((a.clone(), (b.clone(), ()))).unwrap();
    let reverse = JointPolygeroParam::new((b, (a, ()))).unwrap();
    let mut tp = Transcript::for_test(b"joint/late-error");
    let mut rng = DeterministicRng::new(99);
    let mut before_rng = rng.clone();
    let mut invalid = wb.clone();
    invalid.pop();
    assert!(JointPolygeroProver::commit(
        &mut tp.bound(&forward),
        (wa.clone(), (invalid, ())),
        &mut rng
    )
    .is_err());
    assert_eq!(rng.bytes(32), before_rng.bytes(32));
    let mut reversed = Transcript::for_test(b"joint/late-error");
    let (prover, _) = JointPolygeroProver::commit(
        &mut reversed.bound(&forward),
        (wa.clone(), (wb.clone(), ())),
        &mut rng,
    )
    .unwrap();
    assert!(prover
        .prove_drawing(
            &mut reversed.bound(&reverse),
            &(sb.clone(), (sa.clone(), ()))
        )
        .is_err());
    let mut late = Transcript::for_test(b"joint/late-error");
    let (late_prover, _) =
        JointPolygeroProver::commit(&mut late.bound(&forward), (wa, (wb, ())), &mut rng).unwrap();
    let mut invalid = sb;
    invalid.a[0].c = invalid.b.len();
    assert!(late_prover
        .prove_drawing(&mut late.bound(&forward), &(sa, (invalid, ())))
        .is_err());
}

mod participant;

#[test]
fn prover_and_verifier_states_complete_only_on_their_own_session() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let (a, w, statement) = field(&f, &d, 5, config());
    let param = JointPolygeroParam::new((a, ())).unwrap();
    let statements = (statement, ());
    let commit = |t: &mut Transcript| {
        JointPolygeroProver::commit(
            &mut t.bound(&param),
            (w.clone(), ()),
            &mut DeterministicRng::new(3),
        )
        .unwrap()
    };
    // A fork holds the same bytes but is another session.
    let mut stale = Transcript::for_test(b"joint/session");
    let (stale_prover, _) = commit(&mut stale);
    let mut stale_fork = stale.fork_for_test();
    let prover_error = stale_prover
        .prove_drawing(&mut stale_fork.bound(&param), &statements)
        .expect_err("prover state completed on another session");
    assert_eq!(prover_error.0, "joint prover session mismatch");

    let mut tp = Transcript::for_test(b"joint/session");
    let (prover, root) = commit(&mut tp);
    let proof = prover
        .prove_drawing(&mut tp.bound(&param), &statements)
        .unwrap();
    let mut tv = Transcript::for_test(b"joint/session");
    let wrong = JointPolygeroVerifier::receive(&mut tv.bound(&param), &root);
    let mut tv_fork = tv.fork_for_test();
    let verifier_error = wrong
        .reduce_drawing(&mut tv_fork.bound(&param), &proof, &statements)
        .expect_err("verifier state completed on another session");
    assert_eq!(verifier_error.0, "joint verifier session mismatch");
    let mut honest = Transcript::for_test(b"joint/session");
    JointPolygeroVerifier::receive(&mut honest.bound(&param), &root)
        .reduce_drawing(&mut honest.bound(&param), &proof, &statements)
        .unwrap();
}

/// The batching weights are a `Challenge` input (transcript I8): prove and
/// reduce accept them only where they were drawn, and only for statements
/// with the equation counts they were drawn for.
#[test]
fn batching_weights_are_accepted_only_at_their_boundary_and_shape() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let (a, w, statement) = field(&f, &d, 5, config());
    let param = JointPolygeroParam::new((a, ())).unwrap();
    let statements = (statement, ());
    let commit = |t: &mut Transcript| {
        JointPolygeroProver::commit(
            &mut t.bound(&param),
            (w.clone(), ()),
            &mut DeterministicRng::new(3),
        )
        .unwrap()
    };
    // A message after the draw makes the weights stale, in both roles.
    let mut late = Transcript::for_test(b"joint/weights");
    let (stale_prover, root) = commit(&mut late);
    let mut verifier_ts = late.fork_for_test();
    let stale = JointPolygeroParam::weights(&mut late.bound(&param), &statements);
    late.send_for_test(b"late");
    assert!(stale_prover
        .prove(&mut late.bound(&param), stale, &statements)
        .is_err());
    let mut tp = Transcript::for_test(b"joint/weights");
    let (honest_prover, _) = commit(&mut tp);
    let proof = honest_prover
        .prove_drawing(&mut tp.bound(&param), &statements)
        .unwrap();
    let verifier = JointPolygeroVerifier::receive(&mut verifier_ts.bound(&param), &root);
    let stale_verifier = JointPolygeroParam::weights(&mut verifier_ts.bound(&param), &statements);
    verifier_ts.send_for_test(b"late");
    assert!(verifier
        .reduce(
            &mut verifier_ts.bound(&param),
            stale_verifier,
            &proof,
            &statements
        )
        .is_err());
    // Weights drawn for another equation count do not fit the statement.
    let mut short = Transcript::for_test(b"joint/weights");
    let (short_prover, _) = commit(&mut short);
    let mut fewer = statements.clone();
    fewer.0.b.pop();
    fewer.0.a.retain(|term| term.c < fewer.0.b.len());
    let misfit = JointPolygeroParam::weights(&mut short.bound(&param), &fewer);
    let error = short_prover
        .prove(&mut short.bound(&param), misfit, &statements)
        .expect_err("weights for another statement shape");
    assert_eq!(error.0, "batching weights do not fit the statement");
}
