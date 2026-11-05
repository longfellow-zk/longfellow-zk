// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{self, Circuit, Layer, Linear, RawCircuit, Stream},
    },
    runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, RuntimeField},
        polygero::PolygeroConfig,
        random::{DeterministicRng, Transcript},
        zk_v2::ZkContext,
    },
};
#[test]
fn native_shared_prefix_and_every_linear_check_are_authenticated() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.zero()],
        layers: vec![Layer::with_assertions(
            3,
            Stream::default(),
            Stream::<Linear>::from_terms([Linear { g: 0, l: 2, k: 0 }]),
            Stream::default(),
            |_| true,
        )],
    };
    let c = Circuit {
        id: v2::compute_id(&f, &raw),
        raw,
    };
    let part = SharedParticipant::new(
        &c,
        1,
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
        &ctx,
    )
    .unwrap();
    let source = f.one();
    let native = f.zero();
    let mask = f.u64_to_element(17);
    let (state, witness) = part
        .prepare(
            &c,
            vec![source, native],
            mask,
            &mut DeterministicRng::new(42),
            &f,
        )
        .unwrap();
    assert_eq!(witness[..2], [native, mask]);
    assert_eq!(
        witness.len(),
        2 + part.geometry().sc_geom.pad_count().unwrap()
    );
    let mut tp = Transcript::new(b"native-rows");
    let mut tv = tp.clone();
    let reduction = part.reduce(&c, &[f.one()], state, &mut tp, &f).unwrap();
    let checked = part
        .reduce_verify(&c, &[f.one()], &reduction.proof, &mut tv, &f)
        .unwrap();
    assert_eq!(reduction.claim.weights, checked.weights);
    assert_eq!(reduction.claim.target, checked.target);
    let eta = f.u64_to_element(19);
    let mu = reduction.masked_value(&eta, &f);
    let statement = part
        .finish(reduction.claim, &eta, &mu, &mut tp, &f)
        .unwrap();
    let residual = |a: &crate::runtime::polygero::LinearStatement<_>, w: &[_]| {
        let mut x = a.b[0];
        for t in &a.a {
            f.fma(&mut x, &t.k, &w[t.w]);
        }
        x
    };
    assert!(f.is_zero(&residual(&statement, &witness)));
    let pad = statement
        .a
        .iter()
        .find(|a| a.w >= 2 && !f.is_zero(&a.k))
        .unwrap()
        .w;
    let mut bad = witness.clone();
    f.add(&mut bad[pad], &f.one());
    assert!(!f.is_zero(&residual(&statement, &bad)));
    let mut forged = reduction.proof;
    f.add(&mut forged.layers[0].cross, &f.one());
    let mut t = Transcript::new(b"native-rows");
    let claim = part
        .reduce_verify(&c, &[f.one()], &forged, &mut t, &f)
        .unwrap();
    let mu = f.addf(&f.mulf(&eta, &f.mulf(&claim.weights[0], &source)), &mask);
    let statement = part.finish(claim, &eta, &mu, &mut t, &f).unwrap();
    assert!(!f.is_zero(&residual(&statement, &witness)));
}
