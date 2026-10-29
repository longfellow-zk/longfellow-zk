// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::{
            circuit::{compute_id, Circuit, RawCircuit},
            Layer, TermDelta,
        },
    },
    runtime::{
        algebra::{
            fp24_ext6::{RuntimeElement as E, RuntimeFp24Ext6 as F, Q},
            range_interpolation::CrtInterpolatorFactory,
        },
        polygero::PolygeroConfig,
        proto::{dual_packing::PackingProof, zk_v2::ZkProof},
        random::{DeterministicRng, RandomEngine, Transcript},
        zk_v2::{ZkContext, ZkProver, ZkVerifier},
    },
};
fn circuit() -> crate::core::proto::v2::Circuit<F> {
    let f = F::new();
    let raw = RawCircuit {
        ninput: 9,
        npublic_input: 2,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one(), f.mone()],
        layers: vec![Layer::new_compressed(
            9,
            4,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [1, 0],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [0, 2],
                    k_index: 1,
                },
            ]],
            vec![0],
        )],
    };
    crate::core::proto::v2::quadratic_fixture(
        Circuit {
            id: compute_id(&f, &raw),
            raw,
        },
        &f,
    )
}
fn config() -> PolygeroConfig {
    PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    }
}
fn private(f: &F) -> Vec<E> {
    [1, 3, 6, 4, 5, 6, 7]
        .into_iter()
        .map(|v| f.u64_to_element(v))
        .collect()
}
#[test]
fn sextic_public_values_are_unmodified_and_all_authenticated_parts_reject_tampering() {
    let f = F::new();
    let ctx = ZkContext {
        f: &f,
        domain: &CrtInterpolatorFactory,
    };
    let p = ZkProver::new(circuit(), config());
    let public = [f.one(), f.from_coefficients([2, 1, 0, 0, 0, 0])];
    let mut tp = Transcript::new(b"generic/test");
    let (state, g) = p
        .commit(private(&f), &ctx, &mut tp, &mut DeterministicRng::new(412))
        .unwrap();
    let proof = p.prove(&public, state, &mut tp, &ctx).unwrap();
    let bytes = proof.write(&g, &f).unwrap();
    assert_eq!(&bytes[..4], b"LFV4");
    let mut rest = bytes.as_slice();
    let decoded = ZkProof::<3, F>::read(&mut rest, &g, &f).unwrap();
    assert!(rest.is_empty());
    assert_eq!(decoded, proof);
    let verify = |candidate: &ZkProof<3, F>, pubs: &[E]| {
        let mut v = ZkVerifier::new(circuit(), config(), &ctx).unwrap();
        let mut t = Transcript::new(b"generic/test");
        v.receive_commitment(candidate, &mut t);
        v.verify(pubs, candidate, &mut t, &ctx).map(|_| t)
    };
    let mut tv = verify(&proof, &public).unwrap();
    assert_eq!(tp.u128(), tv.u128());
    for i in 0..6 {
        let mut tampered_1 = proof.clone();
        if let PackingProof::TraceZero { u, .. } = &mut tampered_1.packing {
            f.add(&mut u[i], &f.from_coefficients([0, 1, 0, 0, 0, 0]));
        }
        assert!(verify(&tampered_1, &public).is_err());
    }
    let mut tampered_2 = proof.clone();
    if let PackingProof::TraceZero { a, .. } = &mut tampered_2.packing {
        f.add(a, &f.one());
    }
    assert!(verify(&tampered_2, &public).is_err());
    let mut tampered_3 = proof.clone();
    tampered_3.com.root.data[0] ^= 1;
    assert!(verify(&tampered_3, &public).is_err());
    let mut tampered_4 = proof.clone();
    f.add(&mut tampered_4.sumcheck_proof.layers[0].claims[0], &f.one());
    assert!(verify(&tampered_4, &public).is_err());
    let mut tampered_5 = proof.clone();
    f.add(&mut tampered_5.com_proof.h[0], &f.one());
    assert!(verify(&tampered_5, &public).is_err());
    let mut tampered_6 = proof.clone();
    f.add(&mut tampered_6.com_proof.rows[0], &f.one());
    assert!(verify(&tampered_6, &public).is_err());
    let mut changed_public = public;
    f.add(&mut changed_public[1], &f.one());
    assert!(verify(&proof, &changed_public).is_err());
    for n in 0..bytes.len() {
        assert!(ZkProof::<3, F>::read(&mut &bytes[..n], &g, &f).is_err());
    }
    for marker in [b"LFV3", b"LFB4", b"LFM1"] {
        let mut old = bytes.clone();
        old[..4].copy_from_slice(marker);
        assert!(ZkProof::<3, F>::read(&mut old.as_slice(), &g, &f).is_err());
    }
    let mut tampered_7 = bytes;
    let offset = 36 + proof.sumcheck_proof.write(&g.sc_geom, &f).unwrap().len();
    tampered_7[offset..offset + 3].copy_from_slice(&Q.to_le_bytes()[..3]);
    assert!(ZkProof::<3, F>::read(&mut tampered_7.as_slice(), &g, &f).is_err());
}
#[test]
fn invalid_membership_and_public_shapes_do_not_advance_transcript() {
    let f = F::new();
    let ctx = ZkContext {
        f: &f,
        domain: &CrtInterpolatorFactory,
    };
    let p = ZkProver::new(circuit(), config());
    let mut t = Transcript::new(b"invalid");
    let mut original = t.clone();
    let mut rng = DeterministicRng::new(51);
    let mut invalid = private(&f);
    invalid[0] = f.from_coefficients([1, 1, 0, 0, 0, 0]);
    assert!(p.commit(invalid, &ctx, &mut t, &mut rng).is_err());
    assert_eq!(rng.state, 51);
    assert_eq!(t.u128(), original.u128());
    let (state, _) = p.commit(private(&f), &ctx, &mut t, &mut rng).unwrap();
    let mut before_bad_claim = t.clone();
    assert!(p.prove(&[f.one()], state, &mut t, &ctx).is_err());
    assert_eq!(t.u128(), before_bad_claim.u128());
}
#[test]
fn identity_extension_has_no_packing_messages() {
    let f = F::new();
    let ctx = ZkContext {
        f: &f,
        domain: &CrtInterpolatorFactory,
    };
    let p = ZkProver::new_full_field(circuit(), config());
    let public = [f.one(), f.from_coefficients([2, 1, 0, 0, 0, 0])];
    let mut t = Transcript::new(b"identity");
    let (state, g) = p
        .commit(private(&f), &ctx, &mut t, &mut DeterministicRng::new(71))
        .unwrap();
    assert_eq!(g.packing_degree, 1);
    let proof = p.prove(&public, state, &mut t, &ctx).unwrap();
    assert_eq!(proof.packing, PackingProof::Direct);
    let mut v = ZkVerifier::new_full_field(circuit(), config(), &ctx).unwrap();
    let mut tv = Transcript::new(b"identity");
    v.receive_commitment(&proof, &mut tv);
    v.verify(&public, &proof, &mut tv, &ctx).unwrap();
    assert_eq!(t.u128(), tv.u128());
}
#[test]
fn boolean_kernels_match_the_shared_protocol_with_zero_first_input() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
    let raw = RawCircuit {
        ninput: 2,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one()],
        layers: vec![Layer::new_compressed(
            2,
            1,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [1, 0],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 0,
                },
            ]],
            vec![0],
        )],
    };
    let c = Circuit {
        id: compute_id(&f, &raw),
        raw,
    };
    let encoded =
        crate::core::proto::writer::CircuitWriter::new(&f, crate::core::proto::FieldID::Gf2_128)
            .to_bytes_lfc2(&c);
    let fresh = || {
        let c = crate::core::proto::reader::CircuitReader::new(
            &f,
            crate::core::proto::FieldID::Gf2_128,
        )
        .from_bytes_lfc2(&encoded, false)
        .unwrap()
        .0;
        crate::core::proto::v2::quadratic_fixture(c, &f)
    };
    let mut reference = None;
    for window in 0..=4 {
        let mut p = ZkProver::new(
            fresh(),
            PolygeroConfig {
                k: 8,
                s: 2,
                n: 64,
                t: 2,
            },
        );
        if window != 0 {
            p = p.with_boolean_window(window).unwrap();
        }
        let mut t = Transcript::new(b"boolean-kernel");
        let (state, g) = p
            .commit(vec![f.one()], &ctx, &mut t, &mut DeterministicRng::new(52))
            .unwrap();
        let proof = p.prove(&[f.one()], state, &mut t, &ctx).unwrap();
        let bytes = proof.write(&g, &f).unwrap();
        if let Some(r) = &reference {
            assert_eq!(r, &bytes);
        } else {
            reference = Some(bytes);
        }
        let mut v = ZkVerifier::new(
            fresh(),
            PolygeroConfig {
                k: 8,
                s: 2,
                n: 64,
                t: 2,
            },
            &ctx,
        )
        .unwrap();
        let mut tv = Transcript::new(b"boolean-kernel");
        v.receive_commitment(&proof, &mut tv);
        v.verify(&[f.one()], &proof, &mut tv, &ctx).unwrap();
        assert_eq!(t.u128(), tv.u128());
    }
    let p = ZkProver::new(
        crate::core::proto::v2::quadratic_fixture(c, &f),
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
    );
    let mut t = Transcript::new(b"One");
    let (state, _) = p
        .commit(vec![f.one()], &ctx, &mut t, &mut DeterministicRng::new(52))
        .unwrap();
    // Wire zero is an ordinary public input, with no reserved One check.
    p.prove(&[f.zero()], state, &mut t, &ctx).unwrap();
}
