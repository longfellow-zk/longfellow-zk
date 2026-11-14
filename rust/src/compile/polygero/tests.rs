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
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        v2::proto::Digest,
        random::{DeterministicRng, RandomEngine},
        v2::{
            polygero::{
                JointPolygeroParam, JointPolygeroProver, JointPolygeroVerifier, LinearStatement,
                Participant, PolygeroParam,
            },
            transcript::Transcript,
        },
    },
};

#[test]
fn tuning_uses_public_layout_and_respects_capacity() {
    for (nw, bytes) in [(0, 16), (4096, 32), (77000, 16), (162000, 18), (186000, 18)] {
        let selected =
            crate::compile::polygero::tune_large_field(nw, bytes, |p| p.n <= 16384).unwrap();
        assert!(selected.n <= 16384);
        assert_eq!(selected.t, 80);
        let geom = PolygeroGeometry {
            nw,
            k: selected.k,
            s: selected.s,
            n: selected.n,
            t: selected.t,
        };
        assert!(geom.validate().is_ok());
        assert_eq!(
            selected,
            crate::compile::polygero::tune_large_field(nw, bytes, |p| p.n <= 16384).unwrap()
        );
    }
    assert!(crate::compile::polygero::tune_large_field(30, 0, |_| true).is_none());
    assert!(crate::compile::polygero::tune_large_field(30, 16, |_| false).is_none());
}

#[test]
fn rate_tuning_matches_ligero_and_reoptimizes_openings() {
    for (nw, bytes) in [(4096, 32), (77410, 16)] {
        let tune = |accept: fn(PolygeroConfig) -> bool| {
            crate::compile::polygero::tune_large_field_at_rate(7, nw, bytes, accept)
        };
        let selected = tune(|_| true).unwrap();
        assert_eq!(selected.n, 7 * selected.k);
        assert!(selected.t > 80 && selected.t < 132);
        assert_eq!(Some(selected), tune(|_| true));
        assert!(tune(|_| false).is_none());
        let constrained = tune(|p| p.k == 512).unwrap();
        assert_eq!(
            constrained,
            PolygeroConfig {
                k: 512,
                s: 18,
                n: 3584,
                t: 87
            }
        );
    }
    for unsupported in [0, 1, 2, 8, usize::MAX] {
        assert!(
            crate::compile::polygero::tune_large_field_at_rate(unsupported, 3, 32, |_| true,)
                .is_none()
        );
    }
}

#[test]
fn rate_four_tuning_respects_capacity() {
    for nw in [162463, 186358] {
        let tune = |accept: fn(PolygeroConfig) -> bool| {
            crate::compile::polygero::tune_large_field_at_rate(4, nw, 18, accept)
        };
        let selected = tune(|_| true).unwrap();
        assert_eq!(selected.n, 4 * selected.k);
        assert!(2 * selected.t < selected.k);
        assert_eq!(Some(selected), tune(|_| true));
        assert!(tune(|_| false).is_none());
        assert_eq!(
            tune(|p| 2 * p.k + p.s <= 2048 && p.k + p.s <= 1024),
            Some(PolygeroConfig {
                k: 992,
                n: 3968,
                s: 26,
                t: 131
            })
        );
        assert_eq!(
            tune(|p| p.k == 1024),
            Some(PolygeroConfig {
                k: 1024,
                n: 4096,
                s: 27,
                t: 131,
            })
        );
    }
}

#[test]
fn admitted_profiles_encode_and_verify() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    admitted_profiles_roundtrip(&f, &d);
    let prime = crate::runtime::algebra::p256::P256Field::new();
    let extension = crate::runtime::algebra::fp2::Fp2Field::new(&prime);
    use crate::runtime::algebra::SupportsFFT;
    let prime_domain =
        crate::runtime::algebra::range_interpolation::QuadraticExtensionFftInterpolatorFactory::new(
            &prime,
            &extension,
            extension.omega(),
            extension.omega_order(),
        );
    admitted_profiles_roundtrip(&prime, &prime_domain);
    {
        let sextic = crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new();
        admitted_profiles_roundtrip(
            &sextic,
            &crate::runtime::algebra::range_interpolation::CrtInterpolatorFactory,
        );
    }
}

fn admitted_profiles_roundtrip<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    f: &F,
    d: &D,
) {
    let profiles = crate::compile::polygero::profiles::TUNING_PROFILES
        .iter()
        .map(|&(k, s, n)| PolygeroConfig { k, s, n, t: 80 })
        .chain(
            crate::compile::polygero::profiles::RATE7_PROFILES
                .iter()
                .map(|&(k, s, t)| PolygeroConfig { k, s, n: 7 * k, t }),
        )
        .chain(
            crate::compile::polygero::profiles::RATE4_PROFILES
                .iter()
                .map(|&(k, s, t)| PolygeroConfig { k, s, n: 4 * k, t }),
        );
    roundtrip_profiles(f, d, profiles);
}

fn roundtrip_profiles<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    f: &F,
    d: &D,
    profiles: impl IntoIterator<Item = PolygeroConfig>,
) {
    let mut rng = DeterministicRng::new(81409);
    let witness = rng.elt_field_slice(1000, f);
    for config in profiles {
        let statement = Digest::default();
        let param = PolygeroParam::try_new(witness.len(), config, d).unwrap();
        let param = JointPolygeroParam::new((Participant::new(param, d).unwrap(), ())).unwrap();

        let ts = Transcript::new(b"polygero/admitted");
        let (prover, com) =
            JointPolygeroProver::commit(&param, (witness.clone(), ()), ts, &mut rng).unwrap();
        let statements = (
            LinearStatement {
                a: vec![],
                b: vec![],
                digest: statement,
            },
            (),
        );
        let (proof, ts) = prover.prove(&param, &statements).unwrap();
        let bytes = param.write(&proof, ts).unwrap().into_bytes();
        let mut remaining = bytes.as_slice();
        let decoded = param.read(&mut remaining).unwrap();
        assert!(remaining.is_empty());
        let tv = Transcript::new(b"polygero/admitted");
        let verifier = JointPolygeroVerifier::new(param, &com, tv);
        verifier.verify(decoded, &statements).unwrap();
    }
}
