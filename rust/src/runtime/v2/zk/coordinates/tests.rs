// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Coordinate storage: runs, binding, and the expanded claim of a pure-foreign
//! sextic frontend.
use super::*;
use crate::{
    compile::{
        algebra::fp24_ext6::CompileFp24Ext6,
        compiler::{compile_v2, segment_circuit_v2},
        logic::{Logic, LogicIO},
    },
    core::{
        algebra::SupportsU64Conversions,
        proto::v2::{CircuitReader, CircuitWriter},
    },
    runtime::{
        algebra::{
            blas,
            fp24_ext6::{RuntimeElement, RuntimeFp24Ext6},
            packing::{prime24::Prime24Extension, PackingExtension},
            range_interpolation::CrtInterpolatorFactory,
        },
        random::DeterministicRng,
        v2::{
            transcript::{Header, Statement, Transcript, ZkStatement},
            zk::{self, joint::FrontendPart, split::value_count},
        },
    },
};

const CONFIG: PolygeroConfig = PolygeroConfig {
    k: 8,
    s: 2,
    n: 64,
    t: 2,
};

fn group(start: usize, width: usize) -> Group {
    Group::new(start, width).unwrap()
}

/// Two base values, then values with all six coordinates of `width` bits.
fn map(values: usize, base: usize, width: usize) -> CoordinateMap {
    let mut stored = Vec::new();
    let mut at = 100;
    for v in 0..values {
        let coordinates = if v < base { 1 } else { 6 };
        for c in 0..coordinates {
            stored.push((v, c, group(at, width)));
            at += width;
        }
    }
    CoordinateMap::new(values, 6, &stored).unwrap()
}

struct LayoutStatement<'a> {
    identity: ZkStatement<'a>,
    map: &'a CoordinateMap,
}
impl<'a> Statement for LayoutStatement<'a> {
    type Identity = ZkStatement<'a>;
    fn identity(&self) -> &Self::Identity {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.map.write_layout(h);
    }
}

#[test]
fn runs_are_maximal_and_layout_changes_change_the_binding() {
    let m = map(10, 2, 23);
    let runs = m.runs();
    assert_eq!(runs.len(), 2);
    assert_eq!((runs[0].first, runs[0].count, runs[0].start), (0, 2, 100));
    assert_eq!(runs[1].coordinates, (0..6).collect::<Vec<_>>());
    assert_eq!((runs[1].first, runs[1].count, runs[1].start), (2, 8, 146));
    assert_eq!(m.terms(), 2 + 8 * 6);
    let state = |layout: &CoordinateMap, id: [u8; 32]| {
        let statement = LayoutStatement {
            identity: ZkStatement { context: &id },
            map: layout,
        };
        let mut t = Transcript::new(&statement);
        t.borrow().draw(|r| r.bytes(32))
    };
    let base = state(&m, [0; 32]);
    assert_eq!(base, state(&map(10, 2, 23), [0; 32]));
    assert_ne!(base, state(&m, [1; 32]));
    assert_ne!(base, state(&map(10, 3, 23), [0; 32]));
    assert_ne!(base, state(&map(10, 2, 22), [0; 32]));
    assert_ne!(base, state(&map(11, 2, 23), [0; 32]));
    // Coordinates must be increasing, contiguous, and cover every value.
    assert!(CoordinateMap::new(1, 6, &[(0, 1, group(0, 3)), (0, 0, group(3, 3))]).is_err());
    assert!(CoordinateMap::new(1, 6, &[(0, 0, group(0, 3)), (0, 1, group(4, 3))]).is_err());
    assert!(CoordinateMap::new(2, 6, &[(0, 0, group(0, 3))]).is_err());
    assert!(CoordinateMap::new(1, 6, &[(0, 6, group(0, 3))]).is_err());
}

#[test]
fn expanded_claim_holds_on_every_stored_coordinate() {
    let cf = CompileFp24Ext6::new();
    let (raw, _, _) = compile_v2(&cf, |l| {
        let x = l.input(1);
        let y = l.input(2);
        let square = l.precious(&l.mul(&x, &x));
        (l.assert_all("square", &[l.assert_eq("y", &y, &square)]), 1)
    });
    let compiled = segment_circuit_v2(&cf, raw);
    let bytes = CircuitWriter::new(&cf).to_bytes(&compiled);
    let f = RuntimeFp24Ext6::new();
    let (c, _) = CircuitReader::new(&f).from_bytes(&bytes).unwrap();
    let domain = CrtInterpolatorFactory;
    // Private inputs store their base coordinate; pads store all six.
    let m = map(value_count(&c).unwrap(), 2, 23);
    let part =
        zk::split::pure::PureSplit::new(&c, m.storage_map().unwrap(), CONFIG, &domain).unwrap();
    let private = vec![f.u64_to_element(7), f.u64_to_element(49)];
    let state = part
        .prepare(private, &mut DeterministicRng::new(3))
        .unwrap();
    let stored = state.values().to_vec();
    let frontend = FrontendPart::new(&part, &[&c], &[]).unwrap();
    let mut tp = Transcript::new(&ZkStatement {
        context: b"coordinates",
    });
    let mut tv = tp.fork_for_test();
    let mut bp = tp.bound(&frontend);
    let (proof, pending) = zk::split::pure::prover::prove(&mut bp, state).unwrap();
    let linear = pending.claim.batch_linear(&mut bp).unwrap();
    let mut bv = tv.bound(&frontend);
    let claim = zk::split::pure::verifier::reduce(&mut bv, &proof).unwrap();
    let checked = claim.batch_linear(&mut bv).unwrap();
    assert_eq!(linear.weights, checked.weights);
    assert_eq!(linear.target, checked.target);
    let basis = Prime24Extension.native_basis(&f);
    let modular = m.modular_claim(&linear, &basis, &f).unwrap();
    assert_eq!(modular.terms.len(), m.terms());
    assert!(modular.terms.iter().map(|(g, _)| *g).eq(m.groups()));
    let coordinate = |x: &RuntimeElement, index: usize| {
        let mut out = [0; 6];
        out[0] = x.coefficients()[index];
        f.from_coefficients(out)
    };
    let values = m.term_values(&stored, coordinate).unwrap();
    let weights: Vec<_> = modular.terms.iter().map(|(_, k)| *k).collect();
    assert_eq!(blas::dot(&weights, &values, &f), modular.target);
    // Every stored coordinate is bound: changing one breaks the claim.
    for i in 0..values.len() {
        let mut bad = values.clone();
        f.add(&mut bad[i], &f.one());
        assert_ne!(blas::dot(&weights, &bad, &f), modular.target, "term {i}");
    }
}

use crate::runtime::v2::proto::polygero::PolygeroConfig;

#[test]
fn affine_signed_coordinates_pull_back_claims_and_reject_bad_ranges() {
    use crate::runtime::algebra::p256::P256Field;
    let f = P256Field::new();
    let encoding = AffineEncoding::new(2, -8).unwrap();
    let stored: Vec<_> = (0..8).map(|i| (i, 0, group(3 * i, 3), encoding)).collect();
    let map = CoordinateMap::new_affine(8, 1, &stored).unwrap();
    let two = f.u64_to_element(2);
    let eight = f.u64_to_element(8);
    let values: Vec<_> = (0..8)
        .map(|i| f.subf(&f.mulf(&two, &f.u64_to_element(i)), &eight))
        .collect();
    let bits = map.encode_values::<4, _>(&values, |x, _| *x, &f).unwrap();
    assert_eq!(
        bits,
        (0..8).map(|i| f.u64_to_element(i)).collect::<Vec<_>>()
    );
    assert!(map.term_values(&values, |x, _| *x).is_err());
    let weights: Vec<_> = (1..=8).map(|i| f.u64_to_element(i)).collect();
    let claim = LinearClaim {
        target: blas::dot(&weights, &values, &f),
        weights,
    };
    let pulled = map.modular_claim(&claim, &[f.one()], &f).unwrap();
    let scaled: Vec<_> = pulled.terms.iter().map(|(_, w)| *w).collect();
    assert_eq!(blas::dot(&scaled, &bits, &f), pulled.target);
    for i in 0..8 {
        let mut changed = bits.clone();
        f.add(&mut changed[i], &f.one());
        assert_ne!(blas::dot(&scaled, &changed, &f), pulled.target);
    }
    for bad in [f.u64_to_element(8), f.neg(&f.u64_to_element(10)), f.one()] {
        let mut changed = values.clone();
        changed[0] = bad;
        assert!(map.encode_values::<4, _>(&changed, |x, _| *x, &f).is_err());
    }
    let reflected = CoordinateMap::new_affine(
        8,
        1,
        &(0..8)
            .map(|i| (i, 0, group(3 * i, 3), AffineEncoding::new(-2, 8).unwrap()))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let reversed: Vec<_> = values.iter().map(|x| f.neg(x)).collect();
    assert_eq!(
        reflected
            .encode_values::<4, _>(&reversed, |x, _| *x, &f)
            .unwrap(),
        bits
    );
}

#[test]
fn affine_identity_binding_is_unchanged_and_parameters_are_bound() {
    let id = [7; 32];
    let plain = CoordinateMap::new(1, 1, &[(0, 0, group(4, 3))]).unwrap();
    let identity =
        CoordinateMap::new_affine(1, 1, &[(0, 0, group(4, 3), AffineEncoding::IDENTITY)]).unwrap();
    assert_eq!(plain, identity);
    let state = |map: &CoordinateMap| {
        let statement = LayoutStatement {
            identity: ZkStatement { context: &id },
            map,
        };
        let mut t = Transcript::new(&statement);
        t.borrow().draw(|r| r.bytes(32))
    };
    assert_eq!(state(&plain), state(&identity));
    let base = CoordinateMap::new_affine(
        1,
        1,
        &[(0, 0, group(4, 3), AffineEncoding::new(2, -8).unwrap())],
    )
    .unwrap();
    assert_ne!(state(&plain), state(&base));
    for (scale, offset, start, width) in
        [(1, -8, 4, 3), (2, -7, 4, 3), (2, -8, 5, 3), (2, -8, 4, 4)]
    {
        let changed = CoordinateMap::new_affine(
            1,
            1,
            &[(
                0,
                0,
                group(start, width),
                AffineEncoding::new(scale, offset).unwrap(),
            )],
        )
        .unwrap();
        assert_ne!(state(&base), state(&changed));
    }
    assert!(AffineEncoding::new(0, 1).is_err());
    assert!(CoordinateMap::new_affine(
        1,
        1,
        &[(
            0,
            0,
            group(0, 3),
            AffineEncoding {
                scale: 0,
                offset: 1
            }
        )]
    )
    .is_err());
}

#[test]
fn affine_scales_must_not_vanish_in_the_frontend_field() {
    use crate::runtime::algebra::gf2_128::Gf2_128Field;
    let f = Gf2_128Field::new();
    let map = CoordinateMap::new_affine(
        1,
        1,
        &[(0, 0, group(0, 3), AffineEncoding::new(2, -8).unwrap())],
    )
    .unwrap();
    let claim = LinearClaim {
        weights: vec![f.one()],
        target: f.one(),
    };
    assert!(map.modular_claim(&claim, &[f.one()], &f).is_err());
    assert!(map
        .encode_values::<2, _>(&[f.one()], |x, _| *x, &f)
        .is_err());
}

#[test]
fn affine_extension_coordinates_adjust_each_basis_component() {
    let f = RuntimeFp24Ext6::new();
    let mut coefficients = [0; 6];
    coefficients[5] = crate::core::algebra::fp24::Q - 4; // -4 = 2*2-8 modulo q.
    let values = [f.from_coefficients(coefficients)];
    let map = CoordinateMap::new_affine(
        1,
        6,
        &[(0, 5, group(0, 3), AffineEncoding::new(2, -8).unwrap())],
    )
    .unwrap();
    let extract = |x: &RuntimeElement, c: usize| {
        let mut base = [0; 6];
        base[0] = x.coefficients()[c];
        f.from_coefficients(base)
    };
    let encoded = map.encode_values::<3, _>(&values, extract, &f).unwrap();
    assert_eq!(encoded, [f.u64_to_element(2)]);
    let weights = vec![f.from_coefficients([1, 2, 3, 4, 5, 6])];
    let claim = LinearClaim {
        target: blas::dot(&weights, &values, &f),
        weights,
    };
    let basis = Prime24Extension.native_basis(&f);
    let pulled = map.modular_claim(&claim, &basis, &f).unwrap();
    assert_eq!(f.mulf(&pulled.terms[0].1, &encoded[0]), pulled.target);
}
