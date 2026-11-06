// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Ambient-field masking and privacy under witness translations.
use super::*;

struct MaskRng {
    inner: DeterministicRng,
    samples: usize,
}
impl RandomEngine for MaskRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        self.inner.bytes(len)
    }
    fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        self.samples += 1;
        self.inner.elt_field(f)
    }
}

fn ambient_rows<const W: usize, F, D>(f: &F, domain: &D)
where
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
{
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let mut rng = DeterministicRng::new(61723);
    for fixed_prefix in [0, 6, 30] {
        let mut witness = rng.elt_field_slice(30, f);
        for value in &mut witness[..fixed_prefix] {
            *value = f.one();
        }
        let param = PolygeroParam::try_new(witness.len(), config, domain, f).unwrap();
        let geometry = param.geometry();
        let mut mask_rng = MaskRng {
            inner: DeterministicRng::new(42),
            samples: 0,
        };
        let w = super::prover_commitment::encode_rows(
            &param,
            witness.clone(),
            domain,
            &mut mask_rng,
            f,
        );
        let expected_samples = 3 * geometry.k + geometry.s + geometry.t * geometry.data_rows();
        assert_eq!(mask_rng.samples, expected_samples);

        // Recover each ordinary row's logical samples and its unchanged witness.
        let decoder = domain.make_range(geometry.k..2 * geometry.k, 0..geometry.k);
        let width = geometry.row_width();
        for row in 0..geometry.data_rows() {
            let samples = decoder.apply(&w[2 + row][..geometry.k]);
            let end = ((row + 1) * width).min(witness.len());
            assert_eq!(
                &samples[geometry.t..geometry.t + end - row * width],
                &witness[row * width..end]
            );
            assert!(samples[..geometry.t]
                .iter()
                .any(|v| *v != f.zero() && *v != f.one()));
        }
        // Invalid witness lengths fail before consuming randomness or transcript.
        let param = PolygeroParam::try_new(witness.len(), config, domain, f).unwrap();
        let mut invalid = witness;
        invalid.pop();
        let mut rejected_rng = MaskRng {
            inner: DeterministicRng::new(42),
            samples: 0,
        };
        let mut ts = Transcript::new(b"rejected-mask-test");
        let mut original = ts.fork_for_test();
        assert!(JointPolygeroProver::commit(
            &JointPolygeroParam::new((Participant::new(param, f, domain).unwrap(), ())).unwrap(),
            (invalid, ()),
            &mut ts,
            &mut rejected_rng
        )
        .is_err());
        assert_eq!(rejected_rng.samples, 0);
        assert_eq!(ts.bytes(32), original.bytes(32));
    }

    // Six witness changes and two fixed oracle openings determine a degree < 8
    // translation. Its two prefix values translate uniform masks bijectively.
    let mut changes = rng.elt_field_slice(6, f);
    changes.extend([f.zero(), f.zero()]);
    let shifts = domain.make_range(2..10, 0..2).apply(&changes);
    let mut translation = shifts;
    translation.extend_from_slice(&changes[..6]);
    let opened = domain.make_range(0..8, 8..10).apply(&translation);
    assert_eq!(opened, vec![f.zero(); 2]);
}

#[test]
fn binary_ambient_masks_and_privacy() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    ambient_rows(&f, &BinaryInterpolatorFactory::full_field(&f));
}
#[test]
fn extension_ambient_masks_and_privacy() {
    use crate::runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
    };
    ambient_rows(&RuntimeFp24Ext6::new(), &CrtInterpolatorFactory);
}

#[test]
fn ordinary_only_rows_allow_large_mask_prefixes() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let field = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&field);
    let statement = Digest::default();
    let witness = vec![field.one(); 3];
    for t in [4, 5, 7] {
        let config = PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t,
        };
        let param = PolygeroParam::try_new(witness.len(), config, &domain, &field).unwrap();
        let geometry = param.geometry();
        let joint =
            JointPolygeroParam::new((Participant::new(param, &field, &domain).unwrap(), ()))
                .unwrap();
        let mut prover_ts = Transcript::new(b"polygero/ordinary-only");
        let (prover, commitment) = JointPolygeroProver::commit(
            &joint,
            (witness.clone(), ()),
            &mut prover_ts,
            &mut DeterministicRng::new(879),
        )
        .unwrap();
        let proof = prover
            .prove(&joint, &(linear(&[], &[], statement), ()), &mut prover_ts)
            .unwrap();
        assert!(
            proof.bodies.0.rows[2 * geometry.t..(2 + geometry.data_rows()) * geometry.t]
                .iter()
                .any(|value| *value != field.zero() && *value != field.one())
        );
        let bytes = joint
            .write(&proof, prover_ts.fork_for_test())
            .unwrap()
            .into_bytes();
        let mut input = bytes.as_slice();
        let decoded = joint.read(&mut input).unwrap();
        assert!(input.is_empty());
        let mut verifier_ts = Transcript::new(b"polygero/ordinary-only");
        let mut verifier = JointPolygeroVerifier::new(joint);
        verifier.receive_commitment(&commitment, &mut verifier_ts);
        verifier
            .reduce(
                &commitment,
                &decoded,
                &(linear(&[], &[], statement), ()),
                &mut verifier_ts,
            )
            .unwrap();
    }
}
