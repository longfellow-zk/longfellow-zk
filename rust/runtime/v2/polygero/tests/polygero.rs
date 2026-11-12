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

use super::{
    joint::{FieldProof, JointPolygeroProof},
    *,
};
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            range_interpolation::interpolate_range, EvaluationDomain, InterpolationPlan,
            RangeInterpolatorFactory, RuntimeField, SupportsSampling,
        },
        random::{DeterministicRng, RandomEngine},
        v2::{proto::Digest, transcript::Transcript},
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
    fn field(&self) -> &F {
        self.inner.field()
    }
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
    fn field(&self) -> &F {
        self.inner.field()
    }
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
        let polynomial = reference::interpolate(&points, &samples, f);
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
        let witness = rng.elt_field_slice(nw, f);
        let config = PolygeroConfig { k, s, n: 64, t: 2 };
        let statement = Digest { data: [7; 32] };
        let bounded = BoundedDomain {
            inner: backend,
            limit: k + config.n,
        };
        let d = &bounded;
        let p = PolygeroParam::try_new(nw, config, d).unwrap();
        let vp = PolygeroParam::try_new(nw, config, d).unwrap();
        assert_eq!(vp.oracle_range(), k..k + config.n);
        let joint = JointPolygeroParam::new((Participant::new(p, d).unwrap(), ())).unwrap();
        let ts = Transcript::new(b"polygero/test");
        let before = ts.fork_for_test();
        let (prover, com) =
            JointPolygeroProver::commit(&joint, (witness.clone(), ()), ts, &mut rng).unwrap();
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
            let (false_proof, _) = reference::snapshot(&prover)
                .prove(&joint, &(linear(&a, &false_targets, statement), ()))
                .unwrap();
            let verifier = JointPolygeroVerifier::new(joint.clone(), &com, before.fork_for_test());
            let error = verifier
                .reduce(&false_proof, &(linear(&a, &false_targets, statement), ()))
                .err()
                .unwrap();
            assert_eq!(error.0, "Polygero global arithmetic sum failed");
        }
        // Invalid indices cannot produce a completed proving session.
        for (c, w) in [(b.len(), 0), (0, nw), (usize::MAX, 0), (0, usize::MAX)] {
            let invalid = [PolygeroLinearTerm { c, w, k: f.one() }];
            let error = reference::snapshot(&prover)
                .prove(&joint, &(linear(&invalid, &b, statement), ()))
                .err()
                .unwrap();
            assert_eq!(error.0, "linear constraint index out of bounds");
        }
        let counted = CountingDomain {
            inner: d,
            calls: std::cell::RefCell::default(),
        };
        let reference = reference::snapshot(&prover);
        let counted_param =
            JointPolygeroParam::new((Participant::new(vp.clone(), &counted).unwrap(), ())).unwrap();
        let (proof, ts) = prover
            .prove(&counted_param, &(linear(&a, &b, statement), ()))
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
        // Construction binds the root once. A different root or session cannot
        // authenticate an otherwise valid proof.
        let wrong_session = JointPolygeroVerifier::new(
            joint.clone(),
            &com,
            Transcript::new(b"polygero/other-session"),
        );
        assert!(wrong_session
            .reduce(&proof, &(linear(&a, &b, statement), ()))
            .is_err());
        let mut other = com.clone();
        other.root.data[0] ^= 1;
        let wrong_root = JointPolygeroVerifier::new(joint.clone(), &other, before.fork_for_test());
        assert!(wrong_root
            .reduce(&proof, &(linear(&a, &b, statement), ()))
            .is_err());

        if nw != 0 {
            reference::check_recommitted_wrong_witness(
                &joint,
                &reference,
                &b,
                &a,
                &statement,
                before.fork_for_test(),
                f,
            );
        }
        reference::check(&joint, &reference, &proof, &b, &a, &statement, before, d, f);
        let verify = |candidate: &JointPolygeroProof<(FieldProof<F::E>, ())>,
                      targets: &[F::E],
                      constraints: &[PolygeroLinearTerm<F::E>],
                      commitment: &PolygeroCommitment,
                      hash: &Digest| {
            let verifier_param = PolygeroParam::try_new(nw, config, d).unwrap();
            let verifier_param =
                JointPolygeroParam::new((Participant::new(verifier_param, d).unwrap(), ()))
                    .unwrap();
            let v = JointPolygeroVerifier::new(
                verifier_param,
                commitment,
                Transcript::new(b"polygero/test"),
            );
            v.reduce(candidate, &(linear(constraints, targets, *hash), ()))
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
        let (reordered_proof, mut reordered_ts) = reference::snapshot(&reference)
            .prove(&joint, &(linear(&reordered, &b, statement), ()))
            .unwrap();
        assert_eq!(reordered_proof, proof);
        assert_eq!(reordered_ts.bytes(32), ts.fork_for_test().bytes(32));

        let bytes = joint
            .write(&proof, ts.fork_for_test())
            .unwrap()
            .into_bytes();
        let mut input = bytes.as_slice();
        let decoded = joint.read(&mut input).unwrap();
        assert!(input.is_empty());
        assert_eq!(*decoded, proof);
        for which in 0..17 {
            let mut bad = proof.clone();
            match which {
                0 => f.add(&mut bad.bodies.0.h[0], &f.one()),
                1 => f.add(&mut bad.bodies.0.z[0], &f.one()),
                2 => {
                    bad.bodies.0.z.pop();
                }
                3 => f.add(&mut bad.bodies.0.rows[0], &f.one()),
                4 => bad.opening.nonce[0].bytes[0] ^= 1,
                5 => bad.opening.path[0].data[0] ^= 1,
                6 => {
                    bad.bodies.0.h.pop();
                }
                7 => bad.opening.path.push(Digest::default()),
                8 => {
                    bad.bodies.0.rows.pop();
                }
                9 => {
                    // The old column-major layout must not verify as packed rows.
                    bad.bodies.0.rows = (0..vp.geom.t)
                        .flat_map(|query| {
                            proof
                                .bodies
                                .0
                                .rows
                                .chunks_exact(vp.geom.t)
                                .map(move |row| row[query].clone())
                        })
                        .collect();
                }
                10 => {
                    // Query order within each row is fixed by the transcript.
                    for row in bad.bodies.0.rows.chunks_exact_mut(vp.geom.t) {
                        row.swap(0, 1);
                    }
                }
                11 => {
                    // The trailing masking row is transmitted and authenticated.
                    let start = bad.bodies.0.rows.len() - vp.geom.t;
                    f.add(&mut bad.bodies.0.rows[start], &f.one());
                }
                12 => {
                    bad.opening.nonce.pop();
                }
                13 => bad.opening.nonce.push(bad.opening.nonce[0]),
                14 => bad.bodies.0.rows.push(f.zero()),
                15 => bad.bodies.0.h.push(f.zero()),
                16 => bad.bodies.0.z.push(f.zero()),
                _ => unreachable!(),
            }
            let error = verify(&bad, &b, &a, &com, &statement)
                .err()
                .unwrap_or_else(|| panic!("accepted mutation {which}"));
            if which == 11 {
                assert!(error.0.starts_with("root mismatch:"), "{error}");
            } else if (12..17).contains(&which) {
                assert!(error.0 == "joint field proof shape" || error.0 == "joint opening shape");
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
                assert!(joint.read(&mut &bytes[..length]).is_err());
            }
        }
        {
            let mut bad = bytes.clone();
            bad[0] ^= 1;
            assert!(joint.read(&mut bad.as_slice()).is_err());
        }
        {
            let mut bad = bytes.clone();
            bad[4] ^= 1;
            assert!(joint.read(&mut bad.as_slice()).is_err());
        }
        {
            let mut bad = bytes.clone();
            bad[bytes.len() - 1] ^= 1;
            let result = joint.read(&mut bad.as_slice());
            if let Ok(decoded_bad) = result {
                let v = JointPolygeroVerifier::new(
                    joint.clone(),
                    &com,
                    Transcript::new(b"polygero/test"),
                );
                assert!(v
                    .verify(decoded_bad, &(linear(&a, &b, statement), ()))
                    .is_err());
            }
            if !f.is_binary() {
                let mut noncanonical = bytes.clone();
                // The first field element follows the version and context.
                noncanonical[36..36 + f.serialized_size_bytes()].fill(255);
                assert!(joint.read(&mut noncanonical.as_slice()).is_err());
            }
        }
        {
            let mut oversized_frontier = bytes.clone();
            let position = bytes.len() - 32 - proof.opening.path.len() * 32 - 4;
            oversized_frontier[position..position + 4].fill(255);
            assert!(joint.read(&mut oversized_frontier.as_slice()).is_err());
        }
        let invalid = PolygeroConfig {
            t: config.k,
            ..config
        };
        assert!(PolygeroParam::try_new(nw, invalid, d).is_err());
    }
}
#[test]
fn binary_reference_and_failures() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
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
    fn field(&self) -> &F {
        self.inner.field()
    }
    fn domain_id(&self) -> Vec<u8> {
        self.inner.domain_id()
    }
}

#[test]
fn reject_invalid_geometry_and_backend_contracts() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
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
        assert!(PolygeroParam::try_new(2, config, &broken).is_err());
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
        assert!(PolygeroParam::try_new(2, bad, &domain).is_err());
    }
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
    fn field(&self) -> &F {
        self.inner.field()
    }
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
    };
    let f = Gf2_128Field::new();
    let inner = BinaryInterpolatorFactory::full_field(&f);
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
    };
    let f = Gf2_128Field::new();
    let basis: Vec<_> = (0..8)
        .map(|bit| crate::runtime::algebra::gf2_128::Gf2_128::from(1u128 << bit))
        .collect();
    let inner = BinaryInterpolatorFactory::new(&f, &basis);
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
    let witness = rng.elt_field_slice(3, &f);
    let statement = Digest::default();
    let param = PolygeroParam::try_new(3, config, &domain).unwrap();
    assert_eq!(param.oracle_range().end, 256);
    let joint =
        JointPolygeroParam::new((Participant::new(param.clone(), &domain).unwrap(), ())).unwrap();
    let ts = Transcript::new(b"polygero/tight-table");
    let before = ts.fork_for_test();
    let (prover, commitment) =
        JointPolygeroProver::commit(&joint, (witness.clone(), ()), ts, &mut rng).unwrap();
    let constraints = [PolygeroLinearTerm {
        c: 0,
        w: 2,
        k: f.one(),
    }];
    let b = [f.neg(&witness[2])];
    let reference = reference::snapshot(&prover);
    let (proof, _) = prover
        .prove(&joint, &(linear(&constraints, &b, statement), ()))
        .unwrap();
    reference::check(
        &joint,
        &reference,
        &proof,
        &b,
        &constraints,
        &statement,
        before,
        &domain,
        &f,
    );
    let verifier =
        JointPolygeroVerifier::new(joint, &commitment, Transcript::new(b"polygero/tight-table"));
    verifier
        .reduce(&proof, &(linear(&constraints, &b, statement), ()))
        .unwrap();
}

#[path = "masks.rs"]
mod masks;

fn linear<E: Clone>(a: &[PolygeroLinearTerm<E>], b: &[E], digest: Digest) -> LinearStatement<E> {
    LinearStatement {
        a: a.to_vec(),
        b: b.to_vec(),
        digest,
    }
}
#[path = "reference.rs"]
mod reference;

#[test]
fn standalone_statement_owns_its_source_digest() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let p = PolygeroParam::try_new(1, config, &domain).unwrap();
    let param =
        JointPolygeroParam::new((joint::Participant::new(p, &domain).unwrap(), ())).unwrap();
    let statement = LinearStatement::new(
        vec![PolygeroLinearTerm {
            c: 0,
            w: 0,
            k: f.one(),
        }],
        vec![f.one()],
        &f,
    );
    let altered = LinearStatement::new(statement.terms().to_vec(), vec![f.zero()], &f);
    assert_ne!(statement.digest(), altered.digest());
    let seed = b"static-linear-source";
    let (prover, root) = JointPolygeroProver::commit(
        &param,
        (vec![f.one()], ()),
        Transcript::new(seed),
        &mut DeterministicRng::new(42),
    )
    .unwrap();
    let (proof, _) = prover.prove(&param, &(statement.clone(), ())).unwrap();
    JointPolygeroVerifier::new(param.clone(), &root, Transcript::new(seed))
        .reduce(&proof, &(statement, ()))
        .unwrap();
    assert!(
        JointPolygeroVerifier::new(param, &root, Transcript::new(seed))
            .reduce(&proof, &(altered, ()))
            .is_err()
    );
}
