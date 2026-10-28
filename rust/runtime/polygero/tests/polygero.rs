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

use super::*;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            range_interpolation::interpolate_range, EvaluationDomain, InterpolationPlan,
            RangeInterpolatorFactory, RuntimeField, SupportsSampling,
        },
        proto::Digest,
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};

// This wrapper exposes only the range API and enforces the original point-table bound.
// Every core and V2 proof must work with only the original k+n point table.
struct BoundedDomain<'a, D> {
    inner: &'a D,
    limit: usize,
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> RangeInterpolatorFactory<W, F>
    for BoundedDomain<'_, D>
{
    type Plan = D::Plan;
    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        source.end <= self.limit
            && destination.end <= self.limit
            && self.inner.can_interpolate(source, destination)
    }
    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "new domain points requested"
        );
        self.inner.make_range(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        assert!(index < self.limit, "new domain point requested");
        self.inner.point(index)
    }
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> EvaluationDomain<W, F>
    for BoundedDomain<'_, D>
{
    fn domain_id(&self) -> Vec<u8> {
        self.inner.domain_id()
    }
}

fn extend<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>>(
    samples: &[F::E],
    n: usize,
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    if samples.is_empty() {
        vec![f.zero(); n]
    } else {
        interpolate_range(0, samples, 0..n, domain)
    }
}

/// Count plan construction without changing the interpolation backend or points.
struct CountingDomain<'a, D> {
    inner: &'a D,
    calls: std::cell::RefCell<Vec<(std::ops::Range<usize>, std::ops::Range<usize>)>>,
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> RangeInterpolatorFactory<W, F>
    for CountingDomain<'_, D>
{
    type Plan = D::Plan;
    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        self.calls
            .borrow_mut()
            .push((source.clone(), destination.clone()));
        self.inner.make_range(source, destination)
    }
    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        self.inner.can_interpolate(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        self.inner.point(index)
    }
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> EvaluationDomain<W, F>
    for CountingDomain<'_, D>
{
    fn domain_id(&self) -> Vec<u8> {
        self.inner.domain_id()
    }
}

fn exercise<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    f: &F,
    backend: &D,
) {
    let mut rng = DeterministicRng::new(314159);
    let nonzero: Vec<_> = (1..9).map(|i| backend.point(i)).collect();
    let inverses = crate::runtime::algebra::field::batch_inverse(&nonzero, f);
    for (value, inverse) in nonzero.iter().zip(&inverses) {
        assert_eq!(f.mulf(value, inverse), f.one());
    }
    assert!(crate::runtime::algebra::field::batch_inverse::<F>(&[], f).is_empty());
    // Check interpolation independently at prefix and translated physical points.
    for k in [1, 3, 7, 12] {
        let samples = rng.elt_field_slice(k, f);
        let points: Vec<_> = (0..k).map(|i| backend.point(i)).collect();
        let polynomial = super::prover::reference::interpolate(&points, &samples, f);
        let output = extend(&samples, 64, backend, f);
        assert_eq!(&output[..k], samples.as_slice());
        for (i, value) in output.iter().enumerate() {
            let expected = polynomial
                .iter()
                .rev()
                .fold(f.zero(), |a, c| f.addf(c, &f.mulf(&a, &backend.point(i))));
            assert_eq!(*value, expected);
        }
        // Suffix evaluation must match the complete extension across gaps
        // and when either boundary cuts a coset.
        for (n, start) in [
            (64, k),
            (64, k + 1),
            (64, 17),
            (64, 33),
            (63, 62),
            (63, 63),
            (37, 35),
        ] {
            let encoder = backend.make_range(0..k, start..n);
            let suffix = encoder.apply(&samples);
            assert_eq!(suffix, output[start..n]);
        }
    }
    assert!(extend::<W, F, _>(&[], 16, backend, f)
        .iter()
        .all(|x| f.is_zero(x)));
    for (nw, k, s) in [
        (0, 8, 2),
        (1, 3, 2),
        (1, 9, 2),
        (30, 8, 2),
        (30, 9, 2),
        (30, 8, 0),
        (30, 8, 12),
    ] {
        let mut witness = rng.elt_field_slice(nw, f);
        let products = if nw >= 5 {
            witness[2] = f.mulf(&witness[0], &witness[1]);
            witness[3] = f.mulf(&witness[0], &witness[0]);
            witness[4] = f.mulf(&witness[1], &witness[1]);
            (0..9)
                .map(|i| match i % 3 {
                    0 => PolygeroProductConstraint { x: 0, y: 1, z: 2 },
                    1 => PolygeroProductConstraint { x: 0, y: 0, z: 3 },
                    _ => PolygeroProductConstraint { x: 1, y: 1, z: 4 },
                })
                .collect::<Vec<_>>()
        } else {
            vec![]
        };
        let config = PolygeroConfig { k, s, n: 64, t: 2 };
        let statement = Digest { data: [7; 32] };
        let bounded = BoundedDomain {
            inner: backend,
            limit: k + config.n,
        };
        let d = &bounded;
        let p = PolygeroParam::try_new(nw, &products, config, d, f).unwrap();
        let vp = PolygeroParam::try_new(nw, &products, config, d, f).unwrap();
        assert_eq!(vp.oracle_range(), k..k + config.n);
        let mut ts = Transcript::new(b"polygero/test");
        let before = ts.clone();
        let (prover, com) =
            PolygeroProver::commit(witness.clone(), p, &mut ts, d, &mut rng, f).unwrap();
        let mut a = Vec::new();
        let mut b = vec![f.zero(); 3];
        for (w, value) in witness.iter().enumerate() {
            for (c, target) in b.iter_mut().enumerate().take(2) {
                let coefficient = rng.elt_field(f);
                f.sub(target, &f.mulf(&coefficient, value));
                a.push(PolygeroLinearTerm {
                    c,
                    w,
                    k: coefficient,
                });
            }
        }
        {
            // A well-formed but unsatisfied statement is rejected by the verifier.
            let mut false_targets = b.clone();
            f.add(&mut false_targets[2], &f.one());
            let mut false_ts = ts.clone();
            let false_proof = super::prover::reference::snapshot(&prover)
                .prove(&false_targets, &mut false_ts, &a, &statement, d, f)
                .unwrap();
            let mut verifier_ts = before.clone();
            let mut verifier = PolygeroVerifier::new(vp.clone());
            verifier.receive_commitment(&com, &mut verifier_ts);
            let error = verifier
                .verify(
                    &false_targets,
                    &com,
                    &false_proof,
                    &a,
                    &statement,
                    &mut verifier_ts,
                    d,
                    f,
                )
                .unwrap_err();
            assert_eq!(error.0, "Polygero global arithmetic sum failed");
        }
        // Invalid indices still fail before the prover advances the transcript.
        for (c, w) in [(b.len(), 0), (0, nw), (usize::MAX, 0), (0, usize::MAX)] {
            let invalid = [PolygeroLinearTerm { c, w, k: f.one() }];
            let mut rejected_ts = ts.clone();
            let error = super::prover::reference::snapshot(&prover)
                .prove(&b, &mut rejected_ts, &invalid, &statement, d, f)
                .unwrap_err();
            assert_eq!(error.0, "linear constraint index out of bounds");
            assert_eq!(rejected_ts.u128(), ts.clone().u128());
        }
        let counted = CountingDomain {
            inner: d,
            calls: std::cell::RefCell::default(),
        };
        let reference = super::prover::reference::snapshot(&prover);
        let before_prove = ts.clone();
        let proof = prover
            .prove(&b, &mut ts, &a, &statement, &counted, f)
            .unwrap();
        // Public V/z_R evaluations and the two response plans are built once,
        // independently of the number of rows.
        assert_eq!(
            *counted.calls.borrow(),
            vec![
                (vp.oracle_prefix(s + 1), vp.oracle_prefix(k + s)),
                (0..k, k..3 * k),
                (0..k + 1, k..k + config.n),
                (0..k, k..k + config.n),
            ]
        );
        // A verifier must receive this root, even when handed a valid proof.
        let mut unbound = PolygeroVerifier::new(vp.clone());
        let mut unbound_ts = before.clone();
        let missing_root_error = unbound
            .verify(&b, &com, &proof, &a, &statement, &mut unbound_ts, d, f)
            .unwrap_err();
        assert_eq!(missing_root_error.0, "Polygero commitment was not received");
        let mut other = com.clone();
        other.root.data[0] ^= 1;
        unbound.receive_commitment(&other, &mut unbound_ts);
        let mismatched_root_error = unbound
            .verify(&b, &com, &proof, &a, &statement, &mut unbound_ts, d, f)
            .unwrap_err();
        assert_eq!(
            mismatched_root_error.0,
            "Polygero commitment was not received"
        );

        if !products.is_empty() {
            super::prover::reference::check_virtual_product_binding(
                &reference,
                &b,
                &a,
                &statement,
                before.clone(),
                d,
                f,
            );
        }
        super::prover::reference::check(&reference, &proof, &b, &a, &statement, before, d, f);
        let verify = |candidate: &PolygeroProof<F::E>,
                      targets: &[F::E],
                      constraints: &[PolygeroLinearTerm<F::E>],
                      commitment: &PolygeroCommitment,
                      hash: &Digest| {
            let mut verifier_ts = Transcript::new(b"polygero/test");
            let verifier_param = PolygeroParam::try_new(nw, &products, config, d, f).unwrap();
            let mut v = PolygeroVerifier::new(verifier_param);
            v.receive_commitment(commitment, &mut verifier_ts);
            v.verify(
                targets,
                commitment,
                candidate,
                constraints,
                hash,
                &mut verifier_ts,
                d,
                f,
            )
        };
        verify(&proof, &b, &a, &com, &statement).unwrap();

        // Sparse term order and explicit zeros do not change the equations.
        // The source-statement digest is unchanged by either representation.
        let mut reordered = a.clone();
        reordered.reverse();
        if nw != 0 {
            reordered.push(PolygeroLinearTerm {
                c: 0,
                w: 0,
                k: f.zero(),
            });
        }
        verify(&proof, &b, &reordered, &com, &statement).unwrap();
        let mut reordered_ts = before_prove;
        let reordered_proof = super::prover::reference::snapshot(&reference)
            .prove(&b, &mut reordered_ts, &reordered, &statement, d, f)
            .unwrap();
        assert_eq!(reordered_proof, proof);
        assert_eq!(reordered_ts.bytes(32), ts.clone().bytes(32));

        let bytes = proof.write(&vp.geom, f).unwrap();
        let mut input = bytes.as_slice();
        let decoded = crate::runtime::proto::polygero::read(&mut input, &vp.geom, f).unwrap();
        assert!(input.is_empty());
        assert_eq!(decoded, proof);
        for which in 0..if products.is_empty() { 17 } else { 19 } {
            let mut bad = proof.clone();
            match which {
                0 => f.add(&mut bad.h[0], &f.one()),
                1 => f.add(&mut bad.z[0], &f.one()),
                2 => {
                    bad.z.pop();
                }
                3 => f.add(&mut bad.rows[0], &f.one()),
                4 => bad.opening.nonce[0].bytes[0] ^= 1,
                5 => bad.opening.path[0].data[0] ^= 1,
                6 => {
                    bad.h.pop();
                }
                7 => bad.opening.path.push(Digest::default()),
                8 => {
                    bad.rows.pop();
                }
                9 => {
                    // The old column-major layout must not verify as packed rows.
                    bad.rows = (0..vp.geom.t)
                        .flat_map(|query| {
                            proof
                                .rows
                                .chunks_exact(vp.geom.t)
                                .map(move |row| row[query].clone())
                        })
                        .collect();
                }
                10 => {
                    // Query order within each row is fixed by the transcript.
                    for row in bad.rows.chunks_exact_mut(vp.geom.t) {
                        row.swap(0, 1);
                    }
                }
                11 => {
                    // The trailing fstar is transmitted and authenticated even
                    // when no product rows precede it.
                    let start = bad.rows.len() - vp.geom.t;
                    f.add(&mut bad.rows[start], &f.one());
                }
                12 => {
                    bad.opening.nonce.pop();
                }
                13 => bad.opening.nonce.push(bad.opening.nonce[0]),
                14 => bad.rows.push(f.zero()),
                15 => bad.h.push(f.zero()),
                16 => bad.z.push(f.zero()),
                _ => {
                    // Changing either product input changes the reconstructed
                    // output as well; the full committed column must reject it.
                    let row = vp.data_start() + vp.geom.ordinary_rows() + which - 17;
                    f.add(&mut bad.rows[row * vp.geom.t], &f.one());
                }
            }
            let error = verify(&bad, &b, &a, &com, &statement)
                .expect_err(&format!("accepted mutation {which}"));
            if which == 11 {
                assert!(error.0.starts_with("root mismatch:"), "{error}");
            } else if (12..17).contains(&which) {
                assert_eq!(error.0, "Polygero proof shape");
            }
        }
        {
            let mut bad = b.clone();
            f.add(&mut bad[2], &f.one());
            assert!(verify(&proof, &bad, &a, &com, &statement).is_err());
        }
        {
            let mut bad = a.clone();
            bad.push(PolygeroLinearTerm {
                c: 3,
                w: 0,
                k: f.one(),
            });
            assert!(verify(&proof, &b, &bad, &com, &statement).is_err());
        }
        {
            let mut bad = com.clone();
            bad.root.data[0] ^= 1;
            assert!(verify(&proof, &b, &a, &bad, &statement).is_err());
        }
        {
            let mut bad = statement;
            bad.data[0] ^= 1;
            assert!(verify(&proof, &b, &a, &com, &bad).is_err());
            for length in (0..32).chain([bytes.len() / 2, bytes.len() - 1]) {
                assert!(
                    crate::runtime::proto::polygero::read(&mut &bytes[..length], &vp.geom, f)
                        .is_err()
                );
            }
        }
        {
            let mut bad = bytes.clone();
            bad[0] ^= 1;
            assert!(
                crate::runtime::proto::polygero::read(&mut bad.as_slice(), &vp.geom, f).is_err()
            );
        }
        {
            let mut bad = bytes.clone();
            bad[4] ^= 1;
            assert!(
                crate::runtime::proto::polygero::read(&mut bad.as_slice(), &vp.geom, f).is_err()
            );
        }
        {
            let mut bad = bytes.clone();
            bad[bytes.len() - 1] ^= 1;
            let result = crate::runtime::proto::polygero::read(&mut bad.as_slice(), &vp.geom, f);
            if let Ok(decoded_bad) = result {
                assert!(verify(&decoded_bad, &b, &a, &com, &statement).is_err());
            }
            if !f.is_binary() {
                let mut noncanonical = bytes.clone();
                // The first field element follows the version and six u32 counts.
                noncanonical[28..28 + f.serialized_size_bytes()].fill(255);
                assert!(crate::runtime::proto::polygero::read(
                    &mut noncanonical.as_slice(),
                    &vp.geom,
                    f
                )
                .is_err());
            }
        }
        {
            let mut oversized_frontier = bytes.clone();
            let position = bytes.len() - proof.opening.path.len() * 32 - 4;
            oversized_frontier[position..position + 4].fill(255);
            assert!(crate::runtime::proto::polygero::read(
                &mut oversized_frontier.as_slice(),
                &vp.geom,
                f
            )
            .is_err());
        }
        let invalid = PolygeroConfig {
            t: config.k,
            ..config
        };
        assert!(PolygeroParam::try_new(nw, &products, invalid, d, f).is_err());
    }
}
#[test]
fn binary_reference_and_failures() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    exercise(&f, &d);
}
#[test]
fn quadratic_extension_fft_reference_and_failures() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let d = QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    exercise(&f, &d);
}
#[test]
fn q256_scalar_reference_and_failures() {
    use crate::runtime::algebra::{
        q256::Q256Field, range_interpolation::ScalarInterpolatorFactory,
    };
    let f = Q256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    exercise(&f, &d);
}
#[cfg(feature = "experimental")]
#[test]
fn extension_crt_reference_and_failures() {
    use crate::runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
    };
    let f = RuntimeFp24Ext6::new();
    exercise(&f, &CrtInterpolatorFactory);
}

struct BrokenDomain<'a, D> {
    inner: &'a D,
    kind: u8,
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> RangeInterpolatorFactory<W, F>
    for BrokenDomain<'_, D>
{
    type Plan = D::Plan;
    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        assert!(self.can_interpolate(source.clone(), destination.clone()));
        self.inner.make_range(source, destination)
    }
    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        self.kind != 0
            && (self.kind != 1 || source.start == 0)
            && self.inner.can_interpolate(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        self.inner.point(index)
    }
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> EvaluationDomain<W, F>
    for BrokenDomain<'_, D>
{
    fn domain_id(&self) -> Vec<u8> {
        self.inner.domain_id()
    }
}

#[test]
fn reject_invalid_geometry_and_backend_contracts() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    for kind in [0, 1] {
        let broken = BrokenDomain {
            inner: &domain,
            kind,
        };
        assert!(PolygeroParam::try_new(2, &[], config, &broken, &f).is_err());
    }
    for bad in [
        PolygeroConfig {
            k: usize::MAX,
            ..config
        },
        PolygeroConfig { n: 0, ..config },
        PolygeroConfig { t: 0, ..config },
        PolygeroConfig { t: 8, ..config },
    ] {
        assert!(PolygeroParam::try_new(2, &[], bad, &domain, &f).is_err());
    }
    assert!(PolygeroParam::try_new(
        2,
        &[PolygeroProductConstraint { x: 2, y: 0, z: 0 }],
        config,
        &domain,
        &f
    )
    .is_err());
}
#[test]
fn merkle_codecs_bind_role_index_context_and_salt() {
    use crate::runtime::{algebra::gf2_128::Gf2_128Field, proto::MerkleNonce};
    let f = Gf2_128Field::new();
    let context = Digest::default();
    let other = Digest { data: [1; 32] };
    let salt = MerkleNonce { bytes: [7; 32] };
    let other_salt = MerkleNonce { bytes: [8; 32] };
    let column = [f.one()];
    let hash = hash::leaf(&context, 0, &column, &salt, &f);
    assert_ne!(hash, hash::leaf(&context, 1, &column, &salt, &f));
    assert_ne!(hash, hash::leaf(&other, 0, &column, &salt, &f));
    assert_ne!(hash, hash::leaf(&context, 0, &column, &other_salt, &f));
    assert_ne!(hash, hash::node(&context, &context, &other));
    assert_ne!(
        hash::node(&context, &hash, &other),
        hash::node(&context, &other, &hash)
    );
    assert_ne!(
        hash::node(&context, &hash, &other),
        hash::node(&other, &hash, &other)
    );
}

#[test]
fn duplicate_opening_indices_reject_with_polygero_node_hash() {
    use crate::runtime::merkle::{heap::verify_proof_with_hash, MerkleError, MerkleHeap};
    let context = Digest::default();
    let leaves = [Digest { data: [1; 32] }, Digest { data: [2; 32] }];
    let tree = MerkleHeap::new_with_hash(&leaves, |l, r| hash::node(&context, l, r));
    let path = tree.generate_proof(&[0, 1]);
    assert!(verify_proof_with_hash(
        2,
        &tree.root(),
        &path,
        &[(0, leaves[0]), (1, leaves[1])],
        |l, r| hash::node(&context, l, r)
    )
    .is_ok());
    assert_eq!(
        verify_proof_with_hash(
            2,
            &tree.root(),
            &path,
            &[(0, leaves[0]), (0, leaves[0])],
            |l, r| hash::node(&context, l, r)
        ),
        Err(MerkleError::DuplicateLeafIndex { index: 0 })
    );
}

// A global translation of the point table leaves range interpolation unchanged:
// the backend interpolates g(X)=f(X+shift). It need not preserve the obsolete
// point(offset+i)=point(offset)+point(i) condition.
struct ShiftedDomain<'a, const W: usize, F: RuntimeField<W>, D> {
    inner: &'a D,
    field: &'a F,
    shift: F::E,
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> RangeInterpolatorFactory<W, F>
    for ShiftedDomain<'_, W, F, D>
{
    type Plan = D::Plan;
    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        self.inner.can_interpolate(source, destination)
    }
    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        self.inner.make_range(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        self.field.addf(&self.inner.point(index), &self.shift)
    }
}
impl<const W: usize, F: RuntimeField<W> + SerializableField, D: EvaluationDomain<W, F>>
    EvaluationDomain<W, F> for ShiftedDomain<'_, W, F, D>
{
    fn domain_id(&self) -> Vec<u8> {
        let mut id = self.inner.domain_id();
        id.extend(self.field.to_bytes(&self.shift));
        id
    }
}
#[test]
fn translated_point_table_without_translation_contract() {
    use crate::runtime::algebra::{
        gf2_128::{Gf2_128, Gf2_128Field},
        range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let inner = BinaryInterpolatorFactory::new(&f, &sf);
    let domain = ShiftedDomain {
        inner: &inner,
        field: &f,
        shift: Gf2_128::from(1u128 << 100),
    };
    assert_ne!(domain.point(8), f.addf(&domain.point(8), &domain.point(0)));
    exercise(&f, &domain);
}

#[test]
fn binary_profile_fits_exact_original_point_table() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1[..8]);
    let inner = BinaryInterpolatorFactory::new(&f, &sf);
    let domain = BoundedDomain {
        inner: &inner,
        limit: 256,
    };
    let config = PolygeroConfig {
        k: 64,
        s: 8,
        n: 192,
        t: 8,
    };
    assert!(config.can_interpolate(&domain));
    assert!(!domain.can_interpolate(0..config.k, 256..448));
    let mut rng = DeterministicRng::new(963852);
    let mut witness = rng.elt_field_slice(3, &f);
    witness[2] = f.mulf(&witness[0], &witness[1]);
    let products = [PolygeroProductConstraint { x: 0, y: 1, z: 2 }];
    let statement = Digest::default();
    let param = PolygeroParam::try_new(3, &products, config, &domain, &f).unwrap();
    assert_eq!(param.oracle_range().end, 256);
    let verifier_param = param.clone();
    let mut ts = Transcript::new(b"polygero/tight-table");
    let before = ts.clone();
    let (prover, commitment) =
        PolygeroProver::commit(witness.clone(), param, &mut ts, &domain, &mut rng, &f).unwrap();
    let constraints = [PolygeroLinearTerm {
        c: 0,
        w: 2,
        k: f.one(),
    }];
    let b = [f.neg(&witness[2])];
    let reference = super::prover::reference::snapshot(&prover);
    let proof = prover
        .prove(&b, &mut ts, &constraints, &statement, &domain, &f)
        .unwrap();
    super::prover::reference::check(
        &reference,
        &proof,
        &b,
        &constraints,
        &statement,
        before,
        &domain,
        &f,
    );
    let mut verifier_ts = Transcript::new(b"polygero/tight-table");
    let mut verifier = PolygeroVerifier::new(verifier_param);
    verifier.receive_commitment(&commitment, &mut verifier_ts);
    verifier
        .verify(
            &b,
            &commitment,
            &proof,
            &constraints,
            &statement,
            &mut verifier_ts,
            &domain,
            &f,
        )
        .unwrap();
}

#[path = "masks.rs"]
mod masks;
