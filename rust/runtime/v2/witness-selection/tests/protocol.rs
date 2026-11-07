// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{BinaryInterpolatorFactory, ScalarInterpolatorFactory},
            PackingField,
        },
        random::{DeterministicRng, RandomEngine},
        v2::{
            polygero::LinearStatement,
            proto::polygero::PolygeroCommitment,
            transcript::{RoundLabel, Transcript},
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

#[test]
fn generic_sampling_and_three_fields_need_no_packing_capability() {
    use crate::runtime::algebra::{fp_generic::FpGenericField, LIMBS_PER_U64};
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
    let root = PolygeroCommitment {
        root: Digest { data: [3; 32] },
    };
    let a = generic.challenges(&root, &mut Transcript::new(b"generic-sampling").borrow());
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
    let tp = Transcript::new(b"three-fields");
    let (prover, root, responses) = commit(&param, witnesses, tp, &mut rng).unwrap();
    let tv = Transcript::new(b"three-fields");
    let verifier = Verifier::receive(param.clone(), &root, responses, tv);
    let (proof, mut tp) = prover
        .prove(&param, (statement(), (statement(), (statement(), ()))))
        .unwrap();
    let mut tv = verifier
        .authenticate(&proof, (statement(), (statement(), (statement(), ()))))
        .unwrap()
        .into_transcript();
    assert_eq!(tp.u128(), tv.u128());
}

#[test]
fn frontend_cannot_address_fingerprint_masks_and_bad_lengths_do_not_consume_masks() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(3, &f, &d), ())).unwrap();
    let t = Transcript::new(b"shape");
    let mut rng = DeterministicRng::new(1);
    assert!(commit(&param, (vec![f.one(); 5], ()), t, &mut rng).is_err());
    assert_eq!(rng.bytes(32), DeterministicRng::new(1).bytes(32));
    let mut t = Transcript::new(b"shape");
    let root = PolygeroCommitment {
        root: Digest { data: [3; 32] },
    };
    let a = param.challenges(&root, &mut t.borrow());
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
        digest: Digest { data: [0; 32] },
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
    let root = PolygeroCommitment {
        root: Digest { data: [9; 32] },
    };
    let a = param.challenges(&root, &mut Transcript::new(b"cell-coverage").borrow());
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
        let tp = Transcript::new(b"selection/backend");
        let (mut prover, root, mut responses) = commit(&param, witnesses, tp, &mut rng).unwrap();
        let tv = Transcript::new(b"selection/backend");
        if forged > 0 {
            // Rebind the forged response on BOTH sides. Arithmetic rejection is
            // required even when the transcript prefix and final seal agree.
            if forged <= 2 {
                f.add(&mut responses.0.values[forged - 1], &f.one());
            } else {
                p.add(&mut responses.1 .0.values[forged - 3], &p.one());
            }
        }
        let mut verifier = Verifier::receive(param.clone(), &root, responses.clone(), tv);
        if forged == 0 {
            assert_eq!(prover.transcript().u128(), verifier.transcript().u128());
            // Sampling this extra common round is deliberate and symmetric.
        } else {
            // Retain the original committed oracle but authenticate a false row.
            prover
                .backend
                .replace_transcript_for_test(verifier.transcript().fork_for_test());
        }
        let prover = Prover {
            responses,
            ..prover
        };
        let (proof, mut tp) = prover
            .prove(&param, (statement(), (statement(), ())))
            .unwrap();
        let result = verifier.authenticate(&proof, (statement(), (statement(), ())));
        assert_eq!(result.is_ok(), forged == 0);
        if forged == 0 {
            let mut tv = result.unwrap().into_transcript();
            assert_eq!(tp.u128(), tv.u128());
        }
    }
}

#[test]
fn layouts_roots_contexts_and_reader_segmentation_are_bound() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(17, &f, &d), ())).unwrap();
    let root = PolygeroCommitment {
        root: Digest { data: [1; 32] },
    };
    let other = PolygeroCommitment {
        root: Digest { data: [2; 32] },
    };
    let a = param.challenges(&root, &mut Transcript::new(b"layout").borrow());
    let mut changed_identity = param.clone();
    changed_identity.fields.0.field_id.push(0);
    assert_ne!(
        a.0,
        changed_identity
            .challenges(&root, &mut Transcript::new(b"layout").borrow())
            .0
    );
    assert_ne!(
        a.0,
        param
            .challenges(&other, &mut Transcript::new(b"layout").borrow())
            .0
    );
    let different = Param::new((field(18, &f, &d), ())).unwrap();
    assert_ne!(
        a.0[0],
        different
            .challenges(&root, &mut Transcript::new(b"layout").borrow())
            .0[0]
    );
    let mut t = Transcript::new(b"layout");
    let raw = t.round(RoundLabel::Fingerprint, |mut w| {
        w.write_bytes(b"longfellow/witness-selection/v1");
        w.write_bytes(&param.context().data);
        w.write_bytes(&root.root.data);
        w.write_bytes(&1u64.to_le_bytes());
        param.fields.bind_layout(&mut w);
        let mut r = w.begin_squeeze();
        let bytes = r.bytes(2 * 17 * 16);
        r.end_round(bytes)
    });
    let expected: Vec<_> = raw
        .as_chunks::<16>()
        .0
        .iter()
        .map(|x| f.bytes_to_element(x).unwrap())
        .collect();
    assert_eq!(a.0[0], expected[..17]);
    assert_eq!(a.0[1], expected[17..]);
}

#[test]
fn receipt_binds_the_joint_root_once_before_fingerprint_sampling() {
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let param = Param::new((field(17, &f, &d), ())).unwrap();
    let root = PolygeroCommitment {
        root: Digest { data: [7; 32] },
    };
    let responses = (
        FingerprintResponse {
            values: [f.zero(), f.one()],
        },
        (),
    );
    let actual = Transcript::new(b"selection/root-binding");
    let mut verifier = Verifier::receive(param.clone(), &root, responses.clone(), actual);

    // Preserve the existing root framing and order while removing the detached
    // receipt API: the first challenge round must see exactly this prefix.
    let mut expected = Transcript::new(b"selection/root-binding");
    expected.bind(|w| {
        w.write_bytes(b"polygero/joint/root/v1");
        w.write_bytes(&param.context().data);
    });
    expected.bind(|w| w.write_bytes(&root.root.data));
    let _coefficients = param.challenges(&root, &mut expected.borrow());
    param.bind_responses(&responses, &mut expected.borrow());
    assert_eq!(verifier.transcript().round_count_for_test(), 1);
    assert_eq!(verifier.transcript().bytes(32), expected.bytes(32));
}
