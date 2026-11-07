// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            blas,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{BinaryInterpolatorFactory, ScalarInterpolatorFactory},
            Q256Field,
        },
        random::DeterministicRng,
        v2::polygero::{JointPolygeroProver, JointPolygeroVerifier, PolygeroCommitment},
    },
};

impl<S> JointPolygeroProver<S> {
    // Deliberately forged proofs need a matching transcript to exercise the
    // arithmetic checks rather than failing only at commitment authentication.
    pub(crate) fn replace_transcript_for_test(&mut self, transcript: Transcript) {
        self.transcript = transcript;
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
    F: RuntimeField<W> + SerializableField + SupportsSampling,
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
    (
        p,
        w,
        LinearStatement {
            a,
            b,
            digest: Digest {
                data: [n as u8; 32],
            },
        },
    )
}
fn roundtrip<L: Participants + Clone>(p: JointPolygeroParam<L>, w: L::Witnesses, s: L::Statements) {
    let tp = Transcript::new(b"joint/test");
    let tv = tp.fork_for_test();
    let (mut prover, root) =
        JointPolygeroProver::commit(&p, w, tp, &mut DeterministicRng::new(7)).unwrap();
    assert_eq!(prover.transcript().round_count_for_test(), 0);
    let (proof, mut tp) = prover.prove(&p, &s).unwrap();
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
    let mut verifier = JointPolygeroVerifier::new(p.clone(), &root, tv);
    assert_eq!(verifier.transcript().round_count_for_test(), 0);
    let mut tv = verifier.reduce(&decoded, &s).unwrap();
    assert_eq!(tv.round_count_for_test(), 2);
    assert_eq!(tp.u128(), tv.u128());
    let decoded = p.read(&mut bytes.as_slice()).unwrap();
    let full = JointPolygeroVerifier::new(p.clone(), &root, Transcript::new(b"joint/test"));
    full.verify(decoded, &s).unwrap();
    for len in 0..bytes.len() {
        assert!(p.read(&mut &bytes[..len]).is_err(), "prefix {len}");
    }
}
#[test]
fn recursive_one_two_three_and_repeated_fields() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let q = Q256Field::new();
    let qd = ScalarInterpolatorFactory::new(&q, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let (c, wc, sc) = field(&q, &qd, 0, config());
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
    let t = Transcript::new(b"joint/tamper");
    let (prover, root) =
        JointPolygeroProver::commit(&param, (wa, (wb, ())), t, &mut DeterministicRng::new(9))
            .unwrap();
    let (proof, _) = prover.prove(&param, &s).unwrap();
    let verify = |candidate: &JointPolygeroProof<_>, statements: &_| {
        let v = JointPolygeroVerifier::new(param.clone(), &root, Transcript::new(b"joint/tamper"));
        v.reduce(candidate, statements)
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
    bad.1 .0.digest.data[0] ^= 1;
    assert!(verify(&proof, &bad).is_err());
    let mut bad = s.clone();
    p.add(&mut bad.1 .0.b[0], &p.one());
    assert!(verify(&proof, &bad).is_err());
    let mut bad = proof.clone();
    bad.bodies.1 .0.rows.pop();
    assert!(verify(&bad, &s).is_err());
    let mut bad = proof.clone();
    bad.context.data[0] ^= 1;
    assert!(verify(&bad, &s).is_err());
    let original = param.queries(&proof.bodies, &mut Transcript::new(b"queries").borrow());
    let mut changed = false;
    for i in 0..16 {
        let mut bad = proof.clone();
        p.add(&mut bad.bodies.1 .0.z[i], &p.one());
        changed |=
            param.queries(&bad.bodies, &mut Transcript::new(b"queries").borrow()) != original;
    }
    assert!(changed);
    let v = JointPolygeroVerifier::new(param.clone(), &root, Transcript::new(b"wrong-session"));
    assert!(v.reduce(&proof, &s).is_err());
    let mut other = root.clone();
    other.root.data[0] ^= 1;
    let v = JointPolygeroVerifier::new(param, &other, Transcript::new(b"joint/tamper"));
    assert!(v.reduce(&proof, &s).is_err());
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
    let t = Transcript::new(b"invalid");
    let mut rng = DeterministicRng::new(4);
    let mut before_rng = rng.clone();
    let mut bad = w.clone();
    bad.pop();
    assert!(JointPolygeroProver::commit(&param, (bad, ()), t, &mut rng).is_err());
    assert_eq!(rng.bytes(32), before_rng.bytes(32));
    let (prover, _) =
        JointPolygeroProver::commit(&param, (w, ()), Transcript::new(b"invalid"), &mut rng)
            .unwrap();
    let mut bad = s;
    bad.a[0].w = usize::MAX;
    assert!(prover.prove(&param, &(bad, ())).is_err());
}

#[test]
fn forged_linear_witness_is_rejected_even_with_a_genuine_opening() {
    let f = P256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let (a, w, s) = field(&f, &d, 5, config());
    let param = JointPolygeroParam::new((a, ())).unwrap();
    let t = Transcript::new(b"virtual");
    let (mut prover, _) =
        JointPolygeroProver::commit(&param, (w, ()), t, &mut DeterministicRng::new(11)).unwrap();
    let g = param.participants.0.param.geom;
    let z = 2; // First ordinary data row; every row is sent and authenticated.
    for x in &mut prover.states.0[z] {
        f.add(x, &f.one());
    }
    prover.oracle = crate::runtime::v2::polygero::prover_commitment::ColumnOracle::new(
        g.n,
        &param.context,
        &mut DeterministicRng::new(12),
        |j, h| param.participants.append_encoded(&prover.states, j, h),
    );
    let root = PolygeroCommitment {
        root: prover.oracle.root(),
    };
    let mut t = Transcript::new(b"virtual");
    param.receive(&root, &mut t.borrow());
    prover.replace_transcript_for_test(t);
    let (proof, _) = prover.prove(&param, &(s.clone(), ())).unwrap();
    let v = JointPolygeroVerifier::new(param, &root, Transcript::new(b"virtual"));
    let error = v.reduce(&proof, &(s, ())).err().unwrap();
    assert_eq!(error.0, "Polygero global arithmetic sum failed");
}

#[test]
fn tuple_codec_rejects_noncanonical_field_bytes_and_context_changes() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let param = JointPolygeroParam::new((a, (b, ()))).unwrap();
    let t = Transcript::new(b"codec");
    let (prover, _) =
        JointPolygeroProver::commit(&param, (wa, (wb, ())), t, &mut DeterministicRng::new(2))
            .unwrap();
    let (proof, t) = prover.prove(&param, &(sa, (sb, ()))).unwrap();
    let bytes = param.write(&proof, t.fork_for_test()).unwrap().into_bytes();
    let mut bad = bytes.clone();
    let first_prime = 36 + proof.bodies.0.payload_bytes(&f);
    bad[first_prime..first_prime + 32].fill(255);
    assert!(param.read(&mut bad.as_slice()).is_err());
    for position in [0, 4, 35] {
        let mut bad = bytes.clone();
        bad[position] ^= 1;
        assert!(param.read(&mut bad.as_slice()).is_err());
    }
    let mut bad = bytes.clone();
    let n = bad.len();
    bad[n - 4..].fill(255);
    assert!(param.read(&mut bad.as_slice()).is_ok()); // a digest may have arbitrary bytes
    let mut bad = bytes;
    let count_offset = bad.len() - 32 - proof.opening.path.len() * 32 - 4;
    bad[count_offset..count_offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(param.read(&mut bad.as_slice()).is_err());
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
fn all_statements_and_responses_precede_joint_sampling() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let p = P256Field::new();
    let pd = ScalarInterpolatorFactory::new(&p, 128);
    let (a, wa, sa) = field(&f, &d, 17, config());
    let (b, wb, sb) = field(&p, &pd, 5, config());
    let param = JointPolygeroParam::new((a, (b, ()))).unwrap();
    let s = (sa, (sb, ()));
    let tp = Transcript::new(b"joint/order");
    let (mut prover, _root) =
        JointPolygeroProver::commit(&param, (wa, (wb, ())), tp, &mut DeterministicRng::new(98))
            .unwrap();
    let mut manual = prover.transcript().fork_for_test();
    let first = param.challenges(&s, &mut manual.borrow()).0;
    // A change to the last statement must change the first participant's challenges.
    let mut changed = s.clone();
    changed.1 .0.digest.data[0] ^= 1;
    let mut changed_ts = prover.transcript().fork_for_test();
    let changed_challenges = param.challenges(&changed, &mut changed_ts.borrow());
    assert_ne!(first.alpha, changed_challenges.0.alpha);
    let (proof, mut tp) = prover.prove(&param, &s).unwrap();
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
    assert_ne!(forward.context, reverse.context);
    let tp = Transcript::new(b"joint/late-error");
    let mut rng = DeterministicRng::new(99);
    let mut before_rng = rng.clone();
    let mut invalid = wb.clone();
    invalid.pop();
    assert!(
        JointPolygeroProver::commit(&forward, (wa.clone(), (invalid, ())), tp, &mut rng).is_err()
    );
    assert_eq!(rng.bytes(32), before_rng.bytes(32));
    let (prover, _) = JointPolygeroProver::commit(
        &forward,
        (wa.clone(), (wb.clone(), ())),
        Transcript::new(b"joint/late-error"),
        &mut rng,
    )
    .unwrap();
    assert!(prover
        .prove(&reverse, &(sb.clone(), (sa.clone(), ())))
        .is_err());
    let (prover, _) = JointPolygeroProver::commit(
        &forward,
        (wa, (wb, ())),
        Transcript::new(b"joint/late-error"),
        &mut rng,
    )
    .unwrap();
    let mut invalid = sb;
    invalid.a[0].c = invalid.b.len();
    assert!(prover.prove(&forward, &(sa, (invalid, ()))).is_err());
}
