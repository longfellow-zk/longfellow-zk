use std::cell::Cell;

// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use crate::runtime::algebra::{
    gf2_128::Gf2_128RuntimeField, range_interpolation::BinaryInterpolatorFactory,
    subfield_v1::BinarySubfield, ElementOf, InterpolationPlan, RangeInterpolatorFactory,
    RuntimeField, SubfieldV1, SupportsSampling,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        ligero::{
            LigeroCommitment, LigeroConfig, LigeroError, LigeroLinearConstraint, LigeroParam,
            LigeroProof, LigeroProver, LigeroQuadraticConstraint, LigeroVerifier,
        },
        merkle::{Digest, MerkleError},
        random::{RandomEngine, Transcript},
    },
};

struct SimpleRng {
    state: u64,
}
impl RandomEngine for SimpleRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut buf = Vec::with_capacity(len);
        for _ in 0..len {
            self.state = self
                .state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            buf.push((self.state >> 32) as u8);
        }
        buf
    }
}

struct BadInterpolator<I> {
    real: I,
    should_fail: bool,
    fail_on_apply: usize,
    applications: Cell<usize>,
}

impl<const W: usize, F: RuntimeField<W>, I: InterpolationPlan<W, F>> InterpolationPlan<W, F>
    for BadInterpolator<I>
{
    fn apply(&self, source: &[F::E]) -> Vec<F::E> {
        let mut destination = self.real.apply(source);
        self.applications.set(self.applications.get() + 1);
        if self.should_fail && self.applications.get() == self.fail_on_apply {
            destination.rotate_left(1);
        }
        destination
    }
}
struct BadInterpolatorFactory<'a, IF> {
    real: &'a IF,
    calls: Cell<usize>,
    should_fail_at: usize,
    fail_on_apply: usize,
}

impl<const W: usize, F: RuntimeField<W>, IF: RangeInterpolatorFactory<W, F>>
    RangeInterpolatorFactory<W, F> for BadInterpolatorFactory<'_, IF>
{
    type Plan = BadInterpolator<IF::Plan>;

    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        let real = self.real.make_range(source, destination);
        self.calls.set(self.calls.get() + 1);
        BadInterpolator {
            real,
            should_fail: self.calls.get() == self.should_fail_at,
            fail_on_apply: self.fail_on_apply,
            applications: Cell::new(0),
        }
    }

    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        self.real.can_interpolate(source, destination)
    }

    fn point(&self, index: usize) -> F::E {
        self.real.point(index)
    }
}

#[allow(clippy::too_many_arguments)]
fn ligero_test<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    IF: RangeInterpolatorFactory<W, F>,
    SF: SubfieldV1<E = ElementOf<F>>,
>(
    make_interpolator: &IF,
    f: &F,
    sf: &SF,
    nw: usize,
    nq: usize,
    nreq: usize,
    nl: usize,
    block_enc: usize,
) {
    let param = LigeroParam::new(
        nw,
        nq,
        LigeroConfig {
            rateinv: 4,
            nreq,
            block_enc,
        },
        &make_interpolator,
    );

    let mut rng = SimpleRng { state: 42 };

    let mut w = vec![f.zero(); nw];
    let mut a = vec![f.zero(); nw];
    for i in 0..nw {
        w[i] = f.sample(|buf| rng.bytes(buf));
        a[i] = f.sample(|buf| rng.bytes(buf));
    }

    let mut lqc = vec![LigeroQuadraticConstraint { x: 0, y: 0, z: 0 }; nq];
    for i in 0..nq {
        lqc[i].z = 2 * i + 1;
        lqc[i].x = 2 * (((rng.state as usize) % nw) / 2);
        rng.state = rng.state.wrapping_add(1);
        lqc[i].y = 2 * (((rng.state as usize) % nw) / 2);
        rng.state = rng.state.wrapping_add(1);
        w[lqc[i].z] = f.mulf(&w[lqc[i].x], &w[lqc[i].y]);
    }

    let mut llterm = Vec::new();
    let mut b = vec![f.zero(); nl];
    for w_idx in 0..nw {
        let term = LigeroLinearConstraint {
            c: w_idx % nl,
            w: w_idx,
            k: a[w_idx].clone(),
        };
        llterm.push(term);
        b[w_idx % nl] = f.subf(&b[w_idx % nl], &f.mulf(&w[w_idx], &a[w_idx]));
    }

    let mut ts_prover = Transcript::new(b"test");
    let (prover, commitment) = LigeroProver::commit(
        0,
        &w,
        param,
        &mut ts_prover,
        &lqc,
        &make_interpolator,
        &mut rng,
        f,
        sf,
    );

    let hash_of_ligero_statement = Digest {
        data: [
            0xba, 0xad, 0xf0, 0x0d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0,
        ],
    };
    let mut ts_with_zero = ts_prover.clone();
    let proof = prover.prove(
        &b,
        &mut ts_prover,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        f,
    );

    let mut ts_verifier = Transcript::new(b"test");
    let mut verifier = LigeroVerifier::new(&mut ts_verifier, &param);
    verifier.receive_commitment(&commitment);
    let verify_res = verifier.verify(
        &b,
        &commitment,
        &proof,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        f,
    );
    assert_eq!(verify_res, Ok(()));

    let buf_prover = ts_prover.bytes(256);
    let buf_verifier = ts_verifier.bytes(256);
    assert_eq!(
        buf_prover, buf_verifier,
        "Prover and verifier transcripts differ!"
    );

    let serialized = proof
        .write(&param.geom, f, sf)
        .expect("Failed to serialize LigeroProof");

    // Ligero samples one weight per equation and does not bind the term list.
    // Adding a zero term must preserve both the proof bytes and the transcript.
    let mut with_zero = llterm.clone();
    with_zero.push(LigeroLinearConstraint {
        c: 0,
        w: 0,
        k: f.zero(),
    });
    let proof_with_zero = prover.prove(
        &b,
        &mut ts_with_zero,
        &with_zero,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        f,
    );
    assert_eq!(
        proof_with_zero.write(&param.geom, f, sf).unwrap(),
        serialized
    );
    assert_eq!(ts_with_zero.bytes(256), buf_prover);

    let mut r_slice = serialized.as_slice();
    let proof_back = LigeroProof::read(&mut r_slice, &param.geom, f, sf)
        .expect("Failed to deserialize LigeroProof");
    assert!(r_slice.is_empty());

    let mut ts_verifier_back = Transcript::new(b"test");
    let mut verifier_back = LigeroVerifier::new(&mut ts_verifier_back, &param);
    verifier_back.receive_commitment(&commitment);
    let verify_res_back = verifier_back.verify(
        &b,
        &commitment,
        &proof_back,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        f,
    );
    assert_eq!(verify_res_back, Ok(()));

    let buf_verifier_back = ts_verifier_back.bytes(256);
    assert_eq!(
        buf_prover, buf_verifier_back,
        "Prover and verifier_back transcripts differ!"
    );
}

fn test_ligero_verifier_failures_generic<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    IF: RangeInterpolatorFactory<W, F>,
    SF: SubfieldV1<E = ElementOf<F>>,
>(
    make_interpolator: &IF,
    f: &F,
    sf: &SF,
) {
    let nw = 300;
    let nq = 30;
    let nreq = 18;
    let nl = 7;
    let param = LigeroParam::new(
        nw,
        nq,
        LigeroConfig {
            rateinv: 4,
            nreq,
            block_enc: 256,
        },
        &make_interpolator,
    );

    let mut rng = SimpleRng { state: 100 };

    let mut w = vec![f.zero(); nw];
    let mut a = vec![f.zero(); nw];
    for i in 0..nw {
        w[i] = f.sample(|buf| rng.bytes(buf));
        a[i] = f.sample(|buf| rng.bytes(buf));
    }

    let mut lqc = vec![LigeroQuadraticConstraint { x: 0, y: 0, z: 0 }; nq];
    for i in 0..nq {
        lqc[i].z = 3 * i + 2;
        lqc[i].x = 3 * i;
        lqc[i].y = 3 * i + 1;
        w[lqc[i].z] = f.mulf(&w[lqc[i].x], &w[lqc[i].y]);
    }

    let mut llterm = Vec::new();
    let mut b = vec![f.zero(); nl];
    for w_idx in 0..nw {
        let term = LigeroLinearConstraint {
            c: w_idx % nl,
            w: w_idx,
            k: a[w_idx].clone(),
        };
        llterm.push(term);
        b[w_idx % nl] = f.subf(&b[w_idx % nl], &f.mulf(&w[w_idx], &a[w_idx]));
    }

    let mut ts_prover = Transcript::new(b"test");
    let (prover, commitment) = LigeroProver::commit(
        0,
        &w,
        param,
        &mut ts_prover,
        &lqc,
        &make_interpolator,
        &mut rng,
        f,
        sf,
    );

    let hash_of_ligero_statement = Digest {
        data: [
            0xba, 0xad, 0xf0, 0x0d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0,
        ],
    };
    let proof = prover.prove(
        &b,
        &mut ts_prover,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        f,
    );

    // 1. merkle_check failed
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        let mut bad_comm = commitment.clone();
        bad_comm.root.data[0] ^= 1;
        verifier.receive_commitment(&bad_comm);
        let verify_res = verifier.verify(
            &b,
            &bad_comm,
            &proof,
            &llterm,
            &hash_of_ligero_statement,
            &lqc,
            &make_interpolator,
            f,
        );
        match (W, verify_res) {
            (
                2,
                Err(LigeroError::MerkleCheckFailed(MerkleError::ProofLengthMismatch {
                    expected: 46,
                    found: 45,
                })),
            ) => {}
            (
                4,
                Err(LigeroError::MerkleCheckFailed(MerkleError::RootMismatch { expected, found })),
            ) => {
                assert_eq!(expected, bad_comm.root);
                assert_ne!(found, bad_comm.root);
            }
            (_, other) => panic!("wrong error for corrupted Merkle commitment: {other:?}"),
        }
    }

    // 2. wrong dot product
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let mut bad_b = b.clone();
        bad_b[0] = f.addf(&bad_b[0], &f.one());
        let verify_res = verifier.verify(
            &bad_b,
            &commitment,
            &proof,
            &llterm,
            &hash_of_ligero_statement,
            &lqc,
            &make_interpolator,
            f,
        );
        assert_eq!(verify_res, Err(LigeroError::LinearInnerProductMismatch));
    }

    // 3. dot_check failed
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let mut bad_llterm = llterm.clone();
        bad_llterm[0].k = f.addf(&bad_llterm[0].k, &f.one());
        let verify_res = verifier.verify(
            &b,
            &commitment,
            &proof,
            &bad_llterm,
            &hash_of_ligero_statement,
            &lqc,
            &make_interpolator,
            f,
        );
        assert_eq!(verify_res, Err(LigeroError::DotCheckFailed));
    }

    // 4. low_degree_check failed
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let bad_interpolator = BadInterpolatorFactory {
            real: make_interpolator,
            calls: Cell::new(0),
            should_fail_at: 1,
            fail_on_apply: 1,
        };
        let verify_res = verifier.verify(
            &b,
            &commitment,
            &proof,
            &llterm,
            &hash_of_ligero_statement,
            &lqc,
            &bad_interpolator,
            f,
        );
        assert_eq!(verify_res, Err(LigeroError::LowDegreeCheckFailed));
    }

    // 5. quadratic_check failed
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let bad_interpolator = BadInterpolatorFactory {
            real: make_interpolator,
            calls: Cell::new(0),
            should_fail_at: 2,
            fail_on_apply: 2,
        };
        let verify_res = verifier.verify(
            &b,
            &commitment,
            &proof,
            &llterm,
            &hash_of_ligero_statement,
            &lqc,
            &bad_interpolator,
            f,
        );
        assert_eq!(verify_res, Err(LigeroError::QuadraticCheckFailed));
    }

    // 6. out of bounds linear constraint fails cleanly without panicking
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let mut bad_llterm = llterm.clone();
        bad_llterm[0].w = nw + 100;
        let verify_res = verifier.verify(
            &b,
            &commitment,
            &proof,
            &bad_llterm,
            &hash_of_ligero_statement,
            &lqc,
            make_interpolator,
            f,
        );
        assert_eq!(
            verify_res,
            Err(LigeroError::InvalidProof(
                "linear constraint index out of bounds".to_string()
            ))
        );
    }

    // 7. out of bounds quadratic constraint fails cleanly without panicking
    {
        let mut ts = Transcript::new(b"test");
        let mut verifier = LigeroVerifier::new(&mut ts, &param);
        verifier.receive_commitment(&commitment);
        let mut bad_lqc = lqc.clone();
        bad_lqc[0].x = nw + 100;
        let verify_res = verifier.verify(
            &b,
            &commitment,
            &proof,
            &llterm,
            &hash_of_ligero_statement,
            &bad_lqc,
            make_interpolator,
            f,
        );
        assert_eq!(
            verify_res,
            Err(LigeroError::InvalidProof(
                "quadratic constraint index out of bounds".to_string()
            ))
        );
    }
}

#[test]
fn test_rejects_insufficient_blinding_capacity() {
    let nw_hash = 77998;
    let nq_hash = 20;
    let config_hash = crate::runtime::ligero::param::LigeroConfig {
        rateinv: 7,
        nreq: 132,
        block_enc: 451,
    };
    let gf2_runtime = Gf2_128RuntimeField::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let factory = crate::runtime::algebra::range_interpolation::BinaryInterpolatorFactory::new(
        &gf2_runtime,
        &subfield,
    );
    let res = crate::runtime::ligero::param::LigeroParam::try_new(
        nw_hash,
        nq_hash,
        config_hash,
        &factory,
    );
    assert!(res.is_none());
}

#[test]
fn test_ligero_gf2_128() {
    let f = Gf2_128RuntimeField::new();
    let sf = crate::runtime::algebra::subfield_v1::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator = BinaryInterpolatorFactory::new(&f, &sf);
    ligero_test(&make_interpolator, &f, &sf, 3000, 300, 189, 7, 4096);
    test_ligero_verifier_failures_generic(&make_interpolator, &f, &sf);
}

#[test]
fn test_ligero_p256_fft_range() {
    use crate::runtime::algebra::{
        fp2::Fp2Field,
        p256::{P256Field, P256Subfield},
        range_interpolation::QuadraticExtensionFftInterpolatorFactory,
        SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let domain =
        QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    let sf = P256Subfield::new(&f);
    ligero_test(&domain, &f, &sf, 300, 30, 18, 7, 256);
    test_ligero_verifier_failures_generic(&domain, &f, &sf);
}

#[test]
fn test_ligero_scalar_range_only() {
    use crate::runtime::algebra::{
        p256::{P256Field, P256Subfield},
        range_interpolation::ScalarInterpolatorFactory,
    };
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 256);
    let sf = P256Subfield::new(&f);
    ligero_test(&domain, &f, &sf, 300, 30, 18, 7, 256);
    test_ligero_verifier_failures_generic(&domain, &f, &sf);
}

#[test]
fn test_range_capacity_includes_response_source() {
    struct LimitedSource<D> {
        inner: D,
        maximum: usize,
    }
    impl<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>
        RangeInterpolatorFactory<W, F> for LimitedSource<D>
    {
        type Plan = D::Plan;
        fn can_interpolate(
            &self,
            source: std::ops::Range<usize>,
            destination: std::ops::Range<usize>,
        ) -> bool {
            source.len() <= self.maximum && self.inner.can_interpolate(source, destination)
        }
        fn make_range(
            &self,
            source: std::ops::Range<usize>,
            destination: std::ops::Range<usize>,
        ) -> Self::Plan {
            assert!(self.can_interpolate(source.clone(), destination.clone()));
            self.inner.make_range(source, destination)
        }
        fn point(&self, index: usize) -> F::E {
            self.inner.point(index)
        }
    }
    let f = Gf2_128RuntimeField::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let config = LigeroConfig {
        rateinv: 4,
        nreq: 18,
        block_enc: 256,
    };
    let block = (config.block_enc + 1) / (config.rateinv + 2);
    let mut limited = LimitedSource {
        inner: domain,
        maximum: block,
    };
    assert!(limited.can_interpolate(0..block, block..config.block_enc));
    assert!(LigeroParam::try_new(300, 30, config, &limited).is_none());
    limited.maximum = 2 * block - 1;
    ligero_test(&limited, &f, &sf, 300, 30, 18, 7, 256);
}

#[cfg(feature = "experimental")]
#[test]
fn test_ligero_sextic_subfield_matches_full_field_reference() {
    use crate::{
        core::algebra::AlgebraicField,
        runtime::algebra::{
            fp24_ext6::{RuntimeElement, RuntimeFp24Ext6, RuntimeFp24Subfield},
            range_interpolation::CrtInterpolatorFactory,
            RangeInterpolatorFactory,
        },
    };

    fn encode<IF: RangeInterpolatorFactory<3, RuntimeFp24Ext6>>(
        factory: &IF,
        f: &RuntimeFp24Ext6,
        witness: &[RuntimeElement],
        boundary: usize,
        products: &[LigeroQuadraticConstraint],
    ) -> (Digest, Vec<u8>) {
        let sf = RuntimeFp24Subfield;
        let param = LigeroParam::new(
            witness.len(),
            products.len(),
            LigeroConfig {
                rateinv: 4,
                nreq: 2,
                block_enc: 96,
            },
            factory,
        );
        let terms: Vec<_> = (0..witness.len())
            .map(|w| LigeroLinearConstraint {
                c: 0,
                w,
                k: f.one(),
            })
            .collect();
        let b = [witness.iter().fold(f.zero(), |sum, x| f.subf(&sum, x))];
        let statement = Digest { data: [0x42; 32] };
        let mut tp = Transcript::new(b"ligero/subfield-equivalence");
        let (prover, commitment) = LigeroProver::commit(
            boundary,
            witness,
            param,
            &mut tp,
            products,
            factory,
            &mut SimpleRng { state: 42 },
            f,
            &sf,
        );
        let proof = prover.prove(&b, &mut tp, &terms, &statement, products, factory, f);
        let mut tv = Transcript::new(b"ligero/subfield-equivalence");
        let mut verifier = LigeroVerifier::new(&mut tv, &param);
        verifier.receive_commitment(&commitment);
        verifier
            .verify(
                &b,
                &commitment,
                &proof,
                &terms,
                &statement,
                products,
                factory,
                f,
            )
            .unwrap();
        (commitment.root, proof.write(&param.geom, f, &sf).unwrap())
    }

    let f = RuntimeFp24Ext6::new();
    let sf = RuntimeFp24Subfield;
    let mut rng = SimpleRng { state: 314159 };
    for boundary in [0, 40, 80] {
        let mut witness: Vec<_> = (0..80)
            .map(|i| {
                if i < boundary {
                    sf.sample(|n| rng.bytes(n))
                } else {
                    f.sample(|n| rng.bytes(n))
                }
            })
            .collect();
        witness[2] = f.mulf(&witness[0], &witness[1]);
        let products = [LigeroQuadraticConstraint { x: 0, y: 1, z: 2 }];
        // The independent Newton scalar backend uses full-field interpolation.
        // Roots and serialized proofs must agree byte for byte.
        assert_eq!(
            encode(&CrtInterpolatorFactory, &f, &witness, boundary, &products),
            encode(
                &crate::runtime::algebra::range_interpolation::ScalarInterpolatorFactory::new(
                    &f, 96
                ),
                &f,
                &witness,
                boundary,
                &products
            ),
        );
    }
}

#[test]
fn test_cpp_roundtrip_gf2_128() {
    let data = include_bytes!("ligero_test_vector.bin");
    let mut offset = 0;

    let read_u64 = |buf: &[u8], off: &mut usize| {
        let val = u64::from_le_bytes(buf[*off..*off + 8].try_into().unwrap());
        *off += 8;
        val as usize
    };

    let nw = read_u64(data, &mut offset);
    let nq = read_u64(data, &mut offset);
    let nreq = read_u64(data, &mut offset);
    let nl = read_u64(data, &mut offset);
    let subfield_boundary = read_u64(data, &mut offset);

    let f = Gf2_128RuntimeField::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);

    // Read W
    let mut w = Vec::with_capacity(nw);
    for _ in 0..nw {
        let mut slice = &data[offset..];
        let val = crate::runtime::proto::util::read_elt_field(&mut slice, &f).unwrap();
        offset += f.serialized_size_bytes();
        w.push(val);
    }

    // Read A
    let mut a = Vec::with_capacity(nw);
    for _ in 0..nw {
        let mut slice = &data[offset..];
        let val = crate::runtime::proto::util::read_elt_field(&mut slice, &f).unwrap();
        offset += f.serialized_size_bytes();
        a.push(val);
    }

    // Read lqc
    let mut lqc = Vec::with_capacity(nq);
    for _ in 0..nq {
        let x = read_u64(data, &mut offset);
        let y = read_u64(data, &mut offset);
        let z = read_u64(data, &mut offset);
        lqc.push(LigeroQuadraticConstraint { x, y, z });
    }

    // Read llterm
    let llterm_size = read_u64(data, &mut offset);
    let mut llterm = Vec::with_capacity(llterm_size);
    for _ in 0..llterm_size {
        let c = read_u64(data, &mut offset);
        let w_idx = read_u64(data, &mut offset);
        let mut slice = &data[offset..];
        let val = crate::runtime::proto::util::read_elt_field(&mut slice, &f).unwrap();
        offset += f.serialized_size_bytes();
        llterm.push(LigeroLinearConstraint {
            c,
            w: w_idx,
            k: val,
        });
    }

    // Read b
    let mut b = Vec::with_capacity(nl);
    for _ in 0..nl {
        let mut slice = &data[offset..];
        let val = crate::runtime::proto::util::read_elt_field(&mut slice, &f).unwrap();
        offset += f.serialized_size_bytes();
        b.push(val);
    }

    // Read hash_of_ligero_statement
    let mut hash_bytes = [0u8; 32];
    hash_bytes.copy_from_slice(&data[offset..offset + 32]);
    offset += 32;
    let hash_of_ligero_statement = Digest { data: hash_bytes };

    // Read commitment root
    let mut root_bytes = [0u8; 32];
    root_bytes.copy_from_slice(&data[offset..offset + 32]);
    offset += 32;
    let commitment = LigeroCommitment {
        root: Digest { data: root_bytes },
    };

    // Read proof
    let proof_len = read_u64(data, &mut offset);
    let cpp_proof_bytes = &data[offset..offset + proof_len];
    let make_interpolator = BinaryInterpolatorFactory::new(&f, &subfield);
    let param = LigeroParam::new(
        nw,
        nq,
        LigeroConfig {
            rateinv: 4,
            nreq,
            block_enc: 4096,
        },
        &make_interpolator,
    );

    let sf = crate::runtime::algebra::subfield_v1::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    // 1. Deserialize C++ proof using Rust's reader
    let mut r_slice = cpp_proof_bytes;
    let cpp_proof = LigeroProof::read(&mut r_slice, &param.geom, &f, &sf)
        .expect("Failed to deserialize C++ proof");
    assert!(r_slice.is_empty());

    // 2. Verify the C++ proof using Rust verifier
    let mut ts_verifier = Transcript::new(b"test");
    let mut verifier = LigeroVerifier::new(&mut ts_verifier, &param);
    verifier.receive_commitment(&commitment);
    let verify_res = verifier.verify(
        &b,
        &commitment,
        &cpp_proof,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        &f,
    );
    assert_eq!(verify_res, Ok(()));

    // 3. Generate the proof locally in Rust with same seed (100) and check byte compatibility!
    let mut rng = SimpleRng { state: 100 };
    let mut ts_prover = Transcript::new(b"test");
    let (prover, commitment_rust) = LigeroProver::commit(
        subfield_boundary,
        &w,
        param,
        &mut ts_prover,
        &lqc,
        &make_interpolator,
        &mut rng,
        &f,
        &sf,
    );

    assert_eq!(
        commitment_rust.root.data, commitment.root.data,
        "Commitment roots do not match!"
    );

    let proof_rust = prover.prove(
        &b,
        &mut ts_prover,
        &llterm,
        &hash_of_ligero_statement,
        &lqc,
        &make_interpolator,
        &f,
    );

    let rust_proof_bytes = proof_rust
        .write(&param.geom, &f, &sf)
        .expect("Failed to serialize Rust proof");

    assert_eq!(
        rust_proof_bytes, cpp_proof_bytes,
        "Rust proof bytes do not match C++ proof bytes!"
    );
}
