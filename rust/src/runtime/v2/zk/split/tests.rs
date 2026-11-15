// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Split storage: the mixed split of a participant's input equation, and pure
//! foreign storage.
use crate::{
    core::{
        algebra::{AlgebraicField, SupportsU64Conversions},
        proto::v2::{Circuit, Layer, Linear, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{
            p256::P256Field, packing::PackingField, range_interpolation::ScalarInterpolatorFactory,
            RuntimeField, ZkField,
        },
        random::DeterministicRng,
        v2::{
            polygero::{LinearStatement, PolygeroParam},
            proto::polygero::PolygeroConfig,
            transcript::Transcript,
            zk::{
                self,
                joint::{Frontend, FrontendPart, Participant},
                split::{
                    pure::{self, PureSplit},
                    transcript::Eta,
                    value_count, MixedSplit,
                },
                storage::{Group, MixedStorage, StorageMap},
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
        layers: vec![Layer::new(
            3,
            Stream::default(),
            Stream::<Linear>::from_terms([Linear { g: 0, l: 2, k: 0 }]),
            Stream::default(),
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

/// A participant that commits nothing has no Polygero backend (zk I11,
/// audit Z1): a `PureSplit` has no parameter and no `participant`, so it
/// cannot join a joint commitment, and its geometry has no committed cells,
/// not the two fingerprint masks of an empty field.
#[test]
fn pure_foreign_participant_cannot_join_the_joint_backend() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let c = small_circuit(&f);
    let n = value_count(&c).unwrap();
    let groups: Vec<_> = (0..n)
        .map(|i| (i, Group::new(i * 256, 256).unwrap()))
        .collect();
    let storage = StorageMap::new(n, &groups).unwrap();
    let part = PureSplit::new(&c, storage, CONFIG, &domain).unwrap();
    assert!(part.param_for_test().is_none());
    assert_eq!(part.geometry().nw(), 0);
    // A mixed participant still joins, with its native cells, R and the
    // fingerprint masks.
    let mixed = StorageMap::new(n, &[(0, Group::new(7, 1).unwrap())]).unwrap();
    let mask = Group::new(20, 256).unwrap();
    let joined = MixedSplit::new(&c, mixed, mask, CONFIG, &domain).unwrap();
    let committed = joined.param_for_test().unwrap().geometry();
    assert_eq!(committed.nw, joined.geometry().nw());
    let selected = joined.participant(&domain).unwrap();
    assert!(zk::joint::JointParam::new((selected, ())).is_ok());
}

#[test]
fn mixed_split_authenticates_native_rows_and_foreign_values() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let c = small_circuit(&f);
    // Value 0 (the first private input) lives in the binary commitment.
    let shared = Group::new(7, 1).unwrap();
    let mask_group = Group::new(20, 256).unwrap();
    let values = value_count(&c).unwrap();
    let storage = StorageMap::new(values, &[(0, shared)]).unwrap();
    let part = MixedSplit::new(&c, storage, mask_group, CONFIG, &domain).unwrap();
    let source = f.one();
    let native = f.zero();
    let mask = f.u64_to_element(17);
    let (state, witness) = part
        .prepare(vec![source, native], mask, &mut DeterministicRng::new(42))
        .unwrap();
    // Native cells: the native private input, then the pads, then R.
    assert_eq!(witness[0], native);
    assert_eq!(*witness.last().unwrap(), mask);
    assert_eq!(witness.len(), 2 + part.geometry().sumcheck().pad_count());
    let mut tp = Transcript::for_test(b"mixed-rows");
    let mut tv = tp.fork_for_test();
    let (proof, reduction) = zk::prove_split(
        &mut tp.bound(&FrontendPart::new(&part, &[&c], &[f.one()]).unwrap()),
        state,
    )
    .unwrap();
    let checked = zk::reduce_split(
        &mut tv.bound(&FrontendPart::new(&part, &[&c], &[f.one()]).unwrap()),
        &proof,
    )
    .unwrap();
    assert_eq!(reduction.claim.claim.weights, checked.claim.weights);
    assert_eq!(reduction.claim.claim.target, checked.claim.target);
    let eta = Eta(f.u64_to_element(19));
    let mu = part.split_message(&reduction, &eta).unwrap();
    // Foreign claim: eta*w_0*source + R = mu, over the shared group and R.
    let foreign = part.foreign_claim(&checked, &eta, &mu).unwrap();
    assert_eq!(foreign.terms.len(), 2);
    assert_eq!(
        (foreign.terms[0].0, foreign.terms[1].0),
        (shared, mask_group)
    );
    let values = part.foreign_values(&reduction);
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
    let statement = part
        .split_statement(checked, &eta, &mu, tv.session_for_test())
        .unwrap();
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
    let mut t = Transcript::for_test(b"mixed-rows");
    let claim = zk::reduce_split(
        &mut t.bound(&FrontendPart::new(&part, &[&c], &[f.one()]).unwrap()),
        &forged,
    )
    .unwrap();
    let mu = f.addf(
        &f.mulf(&eta.0, &f.mulf(&claim.claim.weights[0], &source)),
        &mask,
    );
    let statement = part
        .split_statement(claim, &eta, &mu, t.session_for_test())
        .unwrap();
    assert!(!holds(&statement, &witness));
}

#[test]
fn pure_foreign_storage_commits_nothing_and_claims_every_value() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let c = small_circuit(&f);
    let values = value_count(&c).unwrap();
    let group = |i: usize| Group::new(256 * i, 256).unwrap();
    let foreign: Vec<_> = (0..values).map(|i| (i, group(i))).collect();
    let storage = StorageMap::new(values, &foreign).unwrap();
    // Each mode takes only its own maps: mixed storage needs a native value,
    // and pure-foreign storage takes no native one.
    assert!(MixedSplit::new(&c, storage.clone(), group(values), CONFIG, &domain).is_err());
    let mixed = StorageMap::new(values, &foreign[1..]).unwrap();
    assert!(PureSplit::new(&c, mixed, CONFIG, &domain).is_err());
    let part = PureSplit::new(&c, storage, CONFIG, &domain).unwrap();
    let public = [f.one()];
    let frontend = FrontendPart::new(&part, &[&c], &public).unwrap();
    let run = || {
        let state = part
            .prepare(
                vec![f.u64_to_element(5), f.zero()],
                &mut DeterministicRng::new(7),
            )
            .unwrap();
        let mut tp = Transcript::for_test(b"pure");
        let mut tv = tp.fork_for_test();
        let mut prover = tp.bound(&frontend);
        let (proof, pending) = pure::prover::prove(&mut prover, state).unwrap();
        let mut verifier = tv.bound(&frontend);
        let claim = pure::verifier::reduce(&mut verifier, &proof).unwrap();
        assert_eq!(pending.claim.claim.weights, claim.claim.weights);
        assert_eq!(pending.claim.claim.target, claim.claim.target);
        // `batch` reads its row weights from the frontend's last stream, as
        // `elements(F, L+1)` (transcript I7), and nothing else.
        let count = pending.claim.row_weight_count();
        let mut reference = prover.transcript().fork_for_test();
        reference
            .borrow()
            .draw(|r| r.elements(&f, count).for_each(drop));
        let witness_values = pending.values.clone();
        let batched = pending.claim.batch(&mut prover);
        assert_eq!(
            prover.transcript().fork_for_test().bytes(32),
            reference.bytes(32)
        );
        let checked = claim.batch(&mut verifier).unwrap();
        (batched, checked, witness_values)
    };
    let (batched, checked, honest) = run();
    let modular = batched.unwrap();
    // The whole claim is foreign, over every value, with its public target,
    // and the honest values satisfy it.
    assert_eq!(modular.terms.len(), values);
    assert_eq!(modular.terms, checked.terms);
    assert_eq!(modular.target, checked.target);
    let mut sum = f.zero();
    for ((_, w), v) in modular.terms.iter().zip(&honest) {
        f.add(&mut sum, &f.mulf(w, v));
    }
    assert_eq!(sum, modular.target);
}

#[test]
fn open_and_receive_draw_eta_and_agree() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let c = small_circuit(&f);
    let values = value_count(&c).unwrap();
    let storage = StorageMap::new(values, &[(0, Group::new(7, 1).unwrap())]).unwrap();
    let mask = Group::new(20, 256).unwrap();
    let part = MixedSplit::new(&c, storage, mask, CONFIG, &domain).unwrap();
    let public = [f.one()];
    let frontend = FrontendPart::new(&part, &[&c], &public).unwrap();
    assert!(std::ptr::eq(frontend.participant, &part));
    assert!(std::ptr::eq(frontend.circuits()[0], &c));
    assert_eq!(&*frontend.public, &public);
    // Both roles draw eta on entry to the split, right after the frontend.
    let run = || {
        let (state, _) = part
            .prepare(
                vec![f.one(), f.zero()],
                f.u64_to_element(17),
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let mut tp = Transcript::for_test(b"split/eta");
        let mut tv = tp.fork_for_test();
        let mut prover = tp.bound(&frontend);
        let (proof, pending) = zk::prove_split(&mut prover, state).unwrap();
        let opened = pending.open(&mut prover);
        let mut verifier = tv.bound(&frontend);
        let claim = zk::reduce_split(&mut verifier, &proof).unwrap();
        let received = match &opened {
            Ok((mu, _)) => Some(claim.receive(&mut verifier, mu)),
            Err(_) => None,
        };
        (opened, received, tp.bytes(32), tv.bytes(32))
    };
    let (honest, received, after_p, after_v) = run();
    let (_, split) = honest.unwrap();
    let checked = received.unwrap().unwrap();
    assert_eq!(split.statement.a, checked.statement.a);
    assert_eq!(split.statement.b, checked.statement.b);
    assert_eq!(split.foreign.terms, checked.foreign.terms);
    assert_eq!(split.foreign.target, checked.foreign.target);
    assert_eq!(after_p, after_v);
}

/// A split state proves only for the participant that prepared it: another
/// participant over the same circuit with another storage map rejects it,
/// although the circuit ID is the same.
#[test]
fn split_state_proves_only_for_its_own_participant() {
    let f = P256Field::new();
    let domain = ScalarInterpolatorFactory::new(&f, 128);
    let c = small_circuit(&f);
    let values = value_count(&c).unwrap();
    let mask = Group::new(20, 256).unwrap();
    let participant = |start| {
        let storage = StorageMap::new(values, &[(0, Group::new(start, 1).unwrap())]).unwrap();
        MixedSplit::new(&c, storage, mask, CONFIG, &domain).unwrap()
    };
    let (own, other) = (participant(7), participant(8));
    assert_eq!(own.geometry(), other.geometry());
    let prove = |part: &MixedSplit<P256Field>| {
        let (state, _) = own
            .prepare(
                vec![f.one(), f.zero()],
                f.u64_to_element(17),
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let mut t = Transcript::for_test(b"split-identity");
        let public = [f.one()];
        let frontend = FrontendPart::new(part, &[&c], &public).unwrap();
        zk::prove_split(&mut t.bound(&frontend), state).map(|_| ())
    };
    assert_eq!(
        prove(&other).unwrap_err(),
        "split state belongs to another participant"
    );
    prove(&own).unwrap();
}

impl<F: ZkField + PackingField> MixedSplit<F> {
    /// Every field, in declaration order: the frontend, the Polygero
    /// parameter and the storage. The pattern is exhaustive, so a new field
    /// does not compile until the statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> (&Frontend<F>, &PolygeroParam, &MixedStorage) {
        let Self {
            frontend,
            param,
            storage,
        } = self;
        (frontend, param, storage)
    }
}
