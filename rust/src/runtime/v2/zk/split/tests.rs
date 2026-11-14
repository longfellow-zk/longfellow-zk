// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Split storage: the mixed split of a participant's input equation, and pure
//! foreign storage.
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{Circuit, Layer, Linear, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{p256::P256Field, range_interpolation::ScalarInterpolatorFactory, RuntimeField},
        random::DeterministicRng,
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            transcript::Transcript,
            zk::{
                joint::CircuitParticipant,
                split::value_count,
                storage::{Group, StorageMap},
                ZkContext,
            },
        },
    },
};

fn small_circuit(f: &P256Field) -> Circuit<P256Field> {
    let raw = RawCircuitBuilder {
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
    }
    .build();
    Circuit::from_raw(f, raw)
}

const CONFIG: PolygeroConfig = PolygeroConfig {
    k: 8,
    s: 2,
    n: 64,
    t: 2,
};

#[test]
fn mixed_split_authenticates_native_rows_and_foreign_values() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let ctx = ZkContext::new(&domain);
    let c = small_circuit(&f);
    // Value 0 (the first private input) lives in the binary commitment.
    let shared = Group { start: 7, width: 1 };
    let mask_group = Group {
        start: 20,
        width: 256,
    };
    let values = value_count(&c).unwrap();
    let storage = StorageMap::new(values, &[(0, shared)]).unwrap();
    let part =
        CircuitParticipant::with_storage(&c, storage, Some(mask_group), CONFIG, &ctx).unwrap();
    assert!(part.commits());
    let source = f.one();
    let native = f.zero();
    let mask = f.u64_to_element(17);
    let (state, witness) = part
        .prepare_split(
            vec![source, native],
            Some(mask),
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    // Native cells: the native private input, then the pads, then R.
    assert_eq!(witness[0], native);
    assert_eq!(*witness.last().unwrap(), mask);
    assert_eq!(
        witness.len(),
        2 + part.geometry().sc_geom.pad_count().unwrap()
    );
    let mut tp = Transcript::new(b"mixed-rows");
    let mut tv = tp.fork_for_test();
    let (proof, reduction) = part
        .prove_split(&c, &[f.one()], state, &mut tp.borrow(), &ctx)
        .unwrap();
    let checked = part
        .reduce_split(&c, &[f.one()], &proof, &mut tv.borrow(), &ctx)
        .unwrap();
    assert_eq!(reduction.claim.claim.weights, checked.claim.weights);
    assert_eq!(reduction.claim.claim.target, checked.claim.target);
    let eta = f.u64_to_element(19);
    let mu = part.split_message(&reduction, &eta, &f).unwrap();
    // Foreign claim: eta*w_0*source + R = mu, over the shared group and R.
    let foreign = part.foreign_claim(&checked, &eta, &mu, &f).unwrap();
    assert_eq!(foreign.terms.len(), 2);
    assert_eq!(
        (foreign.terms[0].0, foreign.terms[1].0),
        (shared, mask_group)
    );
    let values = part.foreign_values(&reduction).unwrap();
    let mut sum = f.zero();
    for ((_, k), v) in foreign.terms.iter().zip(&values) {
        f.fma(&mut sum, k, v);
    }
    assert_eq!(sum, foreign.target);
    // Every row of the statement holds on the witness.
    let holds = |s: &LinearStatement<_>, w: &[_]| {
        let mut rows = s.b.clone();
        for t in &s.a {
            f.fma(&mut rows[t.c], &t.k, &w[t.w]);
        }
        rows.iter().all(|x| f.is_zero(x))
    };
    let statement = part.split_statement(&checked, &eta, &mu, &f).unwrap();
    // The layer rows, unbatched, then the split row.
    assert_eq!(statement.b.len(), c.raw.layers.len() + 1);
    assert!(holds(&statement, &witness));
    // Every native cell is authenticated: changing it breaks some row.
    for cell in 0..witness.len() {
        let mut bad = witness.clone();
        f.add(&mut bad[cell], &f.one());
        assert!(!holds(&statement, &bad), "cell {cell} unauthenticated");
    }
    // A forged sumcheck message changes the claim; the honest split fails.
    let mut forged = proof;
    f.add(&mut forged.layers[0].cross, &f.one());
    let mut t = Transcript::new(b"mixed-rows");
    let claim = part
        .reduce_split(&c, &[f.one()], &forged, &mut t.borrow(), &ctx)
        .unwrap();
    let mu = f.addf(
        &f.mulf(&eta, &f.mulf(&claim.claim.weights[0], &source)),
        &mask,
    );
    let statement = part.split_statement(&claim, &eta, &mu, &f).unwrap();
    assert!(!holds(&statement, &witness));
}

#[test]
fn pure_foreign_storage_commits_nothing_and_claims_every_value() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let ctx = ZkContext::new(&domain);
    let c = small_circuit(&f);
    let values = value_count(&c).unwrap();
    let group = |i: usize| Group {
        start: 256 * i,
        width: 256,
    };
    let foreign: Vec<_> = (0..values).map(|i| (i, group(i))).collect();
    let storage = StorageMap::new(values, &foreign).unwrap();
    // A mask is required exactly when some values are native.
    assert!(CircuitParticipant::with_storage(
        &c,
        storage.clone(),
        Some(group(values)),
        CONFIG,
        &ctx
    )
    .is_err());
    let part = CircuitParticipant::with_storage(&c, storage, None, CONFIG, &ctx).unwrap();
    assert!(!part.commits());
    let private = vec![f.u64_to_element(5), f.zero()];
    let (state, witness) = part
        .prepare_split(private, None, &mut DeterministicRng::new(7))
        .unwrap();
    assert!(witness.is_empty());
    let mut tp = Transcript::new(b"pure");
    let mut tv = tp.fork_for_test();
    let (proof, pending) = part
        .prove_split(&c, &[f.one()], state, &mut tp.borrow(), &ctx)
        .unwrap();
    let claim = part
        .reduce_split(&c, &[f.one()], &proof, &mut tv.borrow(), &ctx)
        .unwrap();
    assert_eq!(pending.claim.claim.weights, claim.claim.weights);
    assert_eq!(pending.claim.claim.target, claim.claim.target);
    // The whole claim is foreign, over every value, with its public target.
    let modular = part.pure_claim(&claim).unwrap();
    assert_eq!(modular.terms.len(), values);
    assert_eq!(modular.target, claim.claim.target);
    // No mask: the mixed split's message and native row do not apply.
    let eta = f.one();
    assert!(part.split_message(&pending, &eta, &f).is_err());
    assert!(part.foreign_claim(&claim, &eta, &eta, &f).is_err());
}
