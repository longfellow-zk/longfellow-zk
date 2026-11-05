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

//! Polygero masks tests.

use super::*;

/// Record which field supplies the masks, independently of the witness values.
struct MaskRng {
    inner: DeterministicRng,
    field_samples: usize,
    subfield_samples: usize,
}
impl RandomEngine for MaskRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        self.inner.bytes(len)
    }
    fn elt_field<const W: usize, F: SupportsSampling<W>>(&mut self, f: &F) -> F::E {
        self.field_samples += 1;
        self.inner.elt_field(f)
    }
    fn elt_subfield<SF: Subfield>(&mut self, sf: &SF) -> SF::E {
        self.subfield_samples += 1;
        self.inner.elt_subfield(sf)
    }
}

fn compact_rows<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling<W>,
    D: EvaluationDomain<W, F>,
    SF: Subfield<E = F::E>,
>(
    f: &F,
    d: &D,
    sf: &SF,
) {
    let mut rng = DeterministicRng::new(61723);
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    // Specialized subfield interpolation must agree with the general encoder.
    for degree in [1, 3, 8, 17] {
        let samples: Vec<_> = (0..degree).map(|_| sf.sample(|n| rng.bytes(n))).collect();
        let encoder = d.make_range(0..degree, degree..128);
        let fast = encoder.apply_subfield(&samples, sf);
        let general = encoder.apply(&samples);
        assert_eq!(fast, general);
    }
    let products = [
        PolygeroProductConstraint { x: 0, y: 1, z: 2 },
        PolygeroProductConstraint { x: 4, y: 3, z: 5 },
        PolygeroProductConstraint { x: 6, y: 7, z: 8 },
        PolygeroProductConstraint { x: 0, y: 20, z: 21 },
        PolygeroProductConstraint {
            x: 22,
            y: 23,
            z: 24,
        },
    ];
    // Full-field slots may happen to contain subfield values. Mask selection
    // must still follow the public boundary, including rows that straddle it.
    for (subfield_boundary, subfield_count) in [
        (0, 0),
        (0, 30),
        (1, 30),
        (5, 30),
        (6, 6),
        (6, 30),
        (9, 9),
        (9, 30),
        (18, 18),
        (18, 30),
        (29, 30),
        (30, 30),
    ] {
        let mut witness = rng.elt_field_slice(30, f);
        for value in &mut witness[..subfield_count] {
            *value = sf.sample(|n| rng.bytes(n));
        }
        for product in &products {
            witness[product.z] = f.mulf(&witness[product.x], &witness[product.y]);
        }
        let statement = Digest { data: [19; 32] };
        let param = PolygeroParam::try_new(30, &products, config, d, f).unwrap();
        let verifier_param = PolygeroParam::try_new(30, &products, config, d, f).unwrap();
        let mut transcript = Transcript::new(b"polygero/compact");
        // Corrupt each declared subfield position in turn. Rejection must
        // precede mask sampling and any change to the transcript.
        for index in 0..subfield_boundary {
            let mut invalid = witness.clone();
            let mut rejection_rng = DeterministicRng::new(106);
            invalid[index] = (0..32)
                .map(|_| rejection_rng.elt_field(f))
                .find(|value| !sf.contains(value))
                .expect("test requires a proper subfield");
            let before_rng = rejection_rng.state;
            let mut rejection_ts = Transcript::new(b"polygero/subfield-rejection");
            let mut before = rejection_ts.clone();
            let rejected = PolygeroProver::commit(
                subfield_boundary,
                invalid,
                param.clone(),
                &mut rejection_ts,
                d,
                &mut rejection_rng,
                f,
                sf,
            );
            assert!(
                matches!(rejected, Err(PolygeroError(ref message)) if message == "witness outside declared subfield")
            );
            assert_eq!(rejection_rng.state, before_rng);
            assert_eq!(before.u128(), rejection_ts.u128());
        }
        let before = transcript.clone();
        let mut mask_rng = MaskRng {
            inner: DeterministicRng::new(95213),
            field_samples: 0,
            subfield_samples: 0,
        };
        let (prover, commitment) = PolygeroProver::commit(
            subfield_boundary,
            witness.clone(),
            param,
            &mut transcript,
            d,
            &mut mask_rng,
            f,
            sf,
        )
        .unwrap();
        let geom = verifier_param.geometry();
        let compact_rows = subfield_boundary / geom.ordinary_width();
        assert_eq!(mask_rng.subfield_samples, geom.t * compact_rows);
        assert_eq!(
            mask_rng.field_samples,
            3 * geom.k
                + geom.s
                + geom.t * (geom.ordinary_rows() - compact_rows + 2 * geom.product_groups()),
        );
        let constraints: Vec<_> = witness
            .iter()
            .enumerate()
            .map(|(w, _)| PolygeroLinearTerm {
                c: 0,
                w,
                k: rng.elt_field(f),
            })
            .collect();
        let mut b = vec![f.zero()];
        for term in &constraints {
            f.sub(&mut b[0], &f.mulf(&term.k, &witness[term.w]));
        }
        let reference = crate::runtime::polygero::prover::reference::snapshot(&prover);
        let proof = prover
            .prove(&b, &mut transcript, &constraints, &statement, d, f)
            .unwrap();
        crate::runtime::polygero::prover::reference::check(
            &reference,
            &proof,
            &b,
            &constraints,
            &statement,
            before,
            d,
            f,
        );
        // Only rows wholly inside the declared subfield portion are compact.
        for row in 0..geom.ordinary_rows() {
            let width = geom.k - geom.t;
            let in_subfield = ((row + 1) * width).min(witness.len()) <= subfield_boundary;
            if in_subfield {
                assert!(proof.rows[(2 + row) * geom.t..(3 + row) * geom.t]
                    .iter()
                    .all(|value| sf.contains(value)));
            } else {
                assert!(proof.rows[(2 + row) * geom.t..(3 + row) * geom.t]
                    .iter()
                    .any(|value| !sf.contains(value)));
            }
        }
        let fstar = geom.transmitted_rows() - 1;
        for row in [0, 1, fstar] {
            assert!(proof.rows[row * geom.t..(row + 1) * geom.t]
                .iter()
                .any(|value| !sf.contains(value)));
        }
        // Product inputs always carry full-field masks, even when every input
        // witness is statically in the subfield. Their output remains virtual.
        for row in
            proof.rows[(2 + geom.ordinary_rows()) * geom.t..fstar * geom.t].chunks_exact(geom.t)
        {
            assert!(row.iter().any(|value| !sf.contains(value)));
        }
        let bytes = proof.write(&geom, f, sf).unwrap();
        let full_bytes = proof.write(&geom, f, &FullField::<W, _>(f)).unwrap();
        if compact_rows > 0 {
            assert!(bytes.len() < full_bytes.len());
        }
        let mut remaining = bytes.as_slice();
        let decoded = crate::runtime::proto::polygero::read(&mut remaining, &geom, f, sf).unwrap();
        assert!(remaining.is_empty());
        assert_eq!(decoded, proof);
        let mut verifier_ts = Transcript::new(b"polygero/compact");
        let mut verifier = PolygeroVerifier::new(verifier_param);
        verifier.receive_commitment(&commitment, &mut verifier_ts);
        verifier
            .verify(
                &b,
                &commitment,
                &decoded,
                &constraints,
                &statement,
                &mut verifier_ts,
                d,
                f,
            )
            .unwrap();
    }
    // Row privacy over the subfield: interpolate a translation which changes
    // the logical witness but fixes the maximum allowed set of opened points.
    // Addition by this fixed subfield mask translation is a bijection.
    let mut samples: Vec<_> = (0..8).map(|_| sf.sample(|n| rng.bytes(n))).collect();
    let original = extend(&samples, config.k + config.n, d, f);
    let points: Vec<_> = (2..8).chain([8, 9]).map(|i| d.point(i)).collect();
    let mut changes: Vec<_> = (2..8).map(|_| sf.sample(|n| rng.bytes(n))).collect();
    changes.extend([f.zero(), f.zero()]);
    let delta = crate::runtime::polygero::prover::reference::interpolate(&points, &changes, f);
    let evaluate_delta = |x: &F::E| {
        delta
            .iter()
            .rev()
            .fold(f.zero(), |acc, c| f.addf(&f.mulf(&acc, x), c))
    };
    let old_samples = samples.clone();
    for (i, value) in samples.iter_mut().enumerate() {
        let shift = evaluate_delta(&d.point(i));
        assert!(sf.contains(&shift));
        f.add(value, &shift);
    }
    let shifted = extend(&samples, config.k + config.n, d, f);
    assert_eq!(&original[8..10], &shifted[8..10]);
    for i in 2..8 {
        assert_eq!(shifted[i], f.addf(&original[i], &changes[i - 2]));
    }
    for (i, value) in samples.iter_mut().enumerate() {
        f.sub(value, &evaluate_delta(&d.point(i)));
    }
    assert_eq!(old_samples, samples);
}

#[test]
fn binary_compact_masks_codec_and_privacy() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    compact_rows(&f, &d, &sf);
    // Domain compatibility cannot silently change a statically subfield row.
    let narrow = BinarySubfield::new(
        &sf.basis()[..8]
            .iter()
            .map(|x| x.to_u128())
            .collect::<Vec<_>>(),
    );
    let param = PolygeroParam::try_new(
        6,
        &[],
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 256,
            t: 2,
        },
        &d,
        &f,
    )
    .unwrap();
    let geometry = param.geometry();
    for subfield_boundary in [1, 5, 6] {
        let mut transcript = Transcript::new(b"polygero/narrow-subfield");
        let mut before = transcript.clone();
        let mut rng = DeterministicRng::new(791);
        let rejected = PolygeroProver::commit(
            subfield_boundary,
            vec![f.one(); 6],
            param.clone(),
            &mut transcript,
            &d,
            &mut rng,
            &f,
            &narrow,
        );
        assert!(
            matches!(rejected, Err(PolygeroError(ref message)) if message == "nonzero subfield_boundary requires a subfield interpolation domain")
        );
        assert_eq!(rng.state, 791);
        assert_eq!(before.u128(), transcript.u128());
    }

    // A zero subfield boundary permits this domain. The ordinary row uses
    // full-field masks even though all six witness values happen to equal one.
    let mut transcript = Transcript::new(b"polygero/narrow-subfield");
    let mut rng = DeterministicRng::new(791);
    let (prover, _) = PolygeroProver::commit(
        0,
        vec![f.one(); 6],
        param,
        &mut transcript,
        &d,
        &mut rng,
        &f,
        &narrow,
    )
    .unwrap();
    let proof = prover
        .prove(&[], &mut transcript, &[], &Digest::default(), &d, &f)
        .unwrap();
    assert!(proof.rows[2 * geometry.t..3 * geometry.t]
        .iter()
        .any(|value| !narrow.contains(value)));
}

#[test]
fn extension_compact_masks_codec_and_privacy() {
    use crate::runtime::algebra::{
        fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Subfield},
        range_interpolation::CrtInterpolatorFactory,
    };
    compact_rows(
        &RuntimeFp24Ext6::new(),
        &CrtInterpolatorFactory,
        &RuntimeFp24Subfield,
    );
}

#[test]
fn ordinary_only_rows_allow_large_mask_prefixes() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield::BinarySubfield,
    };
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&field, &subfield);
    let statement = Digest::default();
    let witness = vec![field.one(); 3];
    for t in [4, 5, 7] {
        let config = PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t,
        };
        let param = PolygeroParam::try_new(witness.len(), &[], config, &domain, &field).unwrap();
        let geometry = param.geometry();
        let verifier_param = param.clone();
        let mut prover_ts = Transcript::new(b"polygero/ordinary-only");
        let (prover, commitment) = PolygeroProver::commit(
            witness.len(),
            witness.clone(),
            param,
            &mut prover_ts,
            &domain,
            &mut DeterministicRng::new(879),
            &field,
            &subfield,
        )
        .unwrap();
        let proof = prover
            .prove(&[], &mut prover_ts, &[], &statement, &domain, &field)
            .unwrap();
        assert!(
            proof.rows[2 * geometry.t..(2 + geometry.ordinary_rows()) * geometry.t]
                .iter()
                .all(|value| subfield.contains(value))
        );
        let bytes = proof.write(&geometry, &field, &subfield).unwrap();
        let mut input = bytes.as_slice();
        let decoded =
            crate::runtime::proto::polygero::read(&mut input, &geometry, &field, &subfield)
                .unwrap();
        assert!(input.is_empty());
        let mut verifier_ts = Transcript::new(b"polygero/ordinary-only");
        let mut verifier = PolygeroVerifier::new(verifier_param);
        verifier.receive_commitment(&commitment, &mut verifier_ts);
        verifier
            .verify(
                &[],
                &commitment,
                &decoded,
                &[],
                &statement,
                &mut verifier_ts,
                &domain,
                &field,
            )
            .unwrap();
    }
}
