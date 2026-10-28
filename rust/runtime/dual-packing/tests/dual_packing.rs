// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Independent trace-adjoint and paper-native equation oracles.
use super::{
    field::{dual_coordinate_numerators, pack, select_bit, trace, unpack, PolynomialBasis128},
    prover::{self, DualPackingMaskValues},
    verifier, AffineClaim, BitLinearClaim, DualPacking128Proof, DUAL_PACKING_MASK_CELLS,
};
use crate::{
    core::{algebra::AlgebraicField, bits::PackedBits},
    runtime::{
        algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};

fn case(
    n: usize,
    seed: u64,
) -> (
    BitLinearClaim,
    PackedBits,
    Vec<E>,
    DualPackingMaskValues,
    [E; DUAL_PACKING_MASK_CELLS],
) {
    let f = F::new();
    let mut rng = DeterministicRng::new(seed);
    let bits: PackedBits = (0..n).map(|_| rng.u128() & 1 != 0).collect();
    let weights: Vec<_> = (0..n).map(|_| E::from(rng.u128())).collect();
    let auxiliary: Vec<_> = (0..3).map(|_| E::from(rng.u128())).collect();
    let terms: Vec<_> = (0..3).map(|i| (i, E::from(rng.u128()))).collect();
    let mut constant = f.zero();
    for (i, &r) in weights.iter().enumerate() {
        f.add(&mut constant, &select_bit(r, bits.get(i)));
    }
    for &(i, k) in &terms {
        f.add(&mut constant, &f.mulf(&k, &auxiliary[i]));
    }
    let claim = BitLinearClaim {
        weights,
        auxiliary_count: auxiliary.len(),
        rhs: AffineClaim { constant, terms },
    };
    let masks = DualPackingMaskValues::sample(&mut rng, &f);
    let cells = masks.cells();
    (claim, bits, auxiliary, masks, cells)
}
/// Direct public coefficient conversion, without the transpose implementation.
fn direct_components(basis: &PolynomialBasis128, weights: &[E], packed: &[E], f: &F) -> [E; 128] {
    let mut result = [f.zero(); 128];
    for (i, row) in weights.chunks(128).enumerate() {
        for (j, r) in row.iter().enumerate() {
            let term = f.mulf(&basis.dual(j), &packed[i]);
            for (k, value) in result.iter_mut().enumerate() {
                if r.bit(k) {
                    f.add(value, &term);
                }
            }
        }
    }
    result
}
/// The paper's L1/L2 literally evaluated, including its dependent t_0.
#[allow(clippy::too_many_arguments)]
fn native_residuals(
    basis: &PolynomialBasis128,
    claim: &BitLinearClaim,
    packed: &[E],
    aux: &[E],
    cells: &[E; 129],
    proof: &DualPacking128Proof,
    delta: &[E; 128],
    f: &F,
) -> [E; 2] {
    let mut t = [f.zero(); 128];
    t[1..].copy_from_slice(&cells[..127]);
    for (j, value) in cells[..127].iter().enumerate() {
        f.add(&mut t[0], &f.mulf(&E::from(1u128 << (j + 1)), value));
    }
    let b = direct_components(basis, &claim.weights, packed, f);
    let target = claim.rhs.evaluate(aux, f).unwrap();
    let mut one = f.addf(&proof.a, &cells[127]);
    let mut two = f.addf(&f.mulf(&proof.a, &proof.a), &cells[128]);
    for k in 0..128 {
        f.add(&mut one, &f.mulf(&delta[k], &t[k]));
        let gamma = f.mulf(&delta[k], &delta[k]);
        let value = f.addf(
            &f.addf(&proof.u[k], &b[k]),
            &f.addf(&f.mulf(&basis.dual(k), &target), &t[k]),
        );
        f.add(&mut two, &f.mulf(&gamma, &value));
    }
    [one, two]
}
fn residuals(
    rows: &[super::PackedLinearClaim; 2],
    packed: &[E],
    aux: &[E],
    cells: &[E; 129],
    f: &F,
) -> [E; 2] {
    std::array::from_fn(|i| rows[i].residual(packed, aux, cells, f).unwrap())
}

#[test]
fn polynomial_coordinates_trace_parity_and_dual_basis() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    for j in 0..128 {
        let word = E::from(1u128 << j);
        let bits = unpack(&[word], 128).unwrap();
        assert_eq!(bits.word128(0), 1u128 << j);
        assert_eq!(pack(&bits), vec![word]);
        assert_eq!(basis.trace_bit(word), trace(word, &f) == f.one());
        for k in 0..128 {
            assert_eq!(
                trace(f.mulf(&basis.dual(j), &E::from(1u128 << k)), &f),
                if j == k { f.one() } else { f.zero() }
            );
        }
    }
    let mut rng = DeterministicRng::new(11);
    for _ in 0..256 {
        let x = E::from(rng.u128());
        assert_eq!(basis.trace_bit(x), trace(x, &f) == f.one());
    }
    assert!(!basis.trace_bit(f.one())); // Degree 128 is even: Tr(1)=0.
    assert!(basis.trace_bit(basis.dual(0)));
}
#[test]
fn transposed_dual_coordinates_match_direct_conversion() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    for rotation in 0..128 {
        let row = std::array::from_fn::<_, 128, _>(|j| E::from(1u128 << ((j + rotation) % 128)));
        for (h, n) in dual_coordinate_numerators(&row).iter().enumerate() {
            assert_eq!(
                f.mulf(&basis.dual(127), n),
                basis.dual((h + 128 - rotation) % 128)
            );
        }
    }
    for n in [0, 1, 7, 63, 127, 128] {
        let mut rng = DeterministicRng::new(n as u64 + 519);
        let row = (0..n).map(|_| E::from(rng.u128())).collect::<Vec<_>>();
        for (h, numerator) in dual_coordinate_numerators(&row).iter().enumerate() {
            let mut expected = f.zero();
            for (j, r) in row.iter().enumerate() {
                f.add(&mut expected, &select_bit(basis.dual(j), r.bit(h)));
            }
            assert_eq!(f.mulf(&basis.dual(127), numerator), expected);
        }
    }
}
#[test]
fn components_are_the_papers_trace_adjoint_forms() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    for n in [0, 1, 7, 127, 128, 129, 257, 513] {
        let (claim, bits, aux, _, _) = case(n, n as u64 + 19);
        let packed = pack(&bits);
        let actual = prover::components(&basis, &claim.weights, &bits, &f);
        assert_eq!(
            actual,
            direct_components(&basis, &claim.weights, &packed, &f)
        );
        let target = claim.rhs.evaluate(&aux, &f).unwrap();
        for (k, &b) in actual.iter().enumerate() {
            assert_eq!(basis.trace_bit(b), target.bit(k));
        }
    }
}
#[test]
fn expanded_rows_equal_native_paper_equations_for_arbitrary_cells() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let mut rng = DeterministicRng::new(918);
    for n in [0, 1, 7, 127, 128, 129, 257] {
        let (mut claim, bits, aux, _, _) = case(n, n as u64 + 27);
        let packed = pack(&bits);
        // False targets and unrelated r,b are deliberately permitted here.
        f.add(&mut claim.rhs.constant, &f.one());
        let cells = std::array::from_fn(|_| E::from(rng.u128()));
        let proof = DualPacking128Proof {
            u: std::array::from_fn(|_| E::from(rng.u128())),
            a: E::from(rng.u128()),
        };
        for kind in 0..4 {
            let delta = std::array::from_fn(|k| match kind {
                0 => f.zero(),
                1 => f.one(),
                2 => E::from(1u128 << k),
                _ => E::from(rng.u128()),
            });
            let rows = super::reconstruct(&basis, &claim, &proof, &delta, &f);
            assert_eq!(
                residuals(&rows, &packed, &aux, &cells, &f),
                native_residuals(&basis, &claim, &packed, &aux, &cells, &proof, &delta, &f)
            );
        }
    }
}
#[test]
fn honest_native_equations_allow_zero_and_one_challenges() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let (claim, bits, aux, masks, cells) = case(193, 4);
    let t = masks.coordinates(&f);
    let target = claim.rhs.evaluate(&aux, &f).unwrap();
    let b = prover::components(&basis, &claim.weights, &bits, &f);
    let u = std::array::from_fn(|k| {
        f.addf(
            &f.addf(&b[k], &f.mulf(&basis.dual(k), &target)),
            &f.addf(&t[k], &f.mulf(&t[k], &t[k])),
        )
    });
    for delta in [[f.zero(); 128], [f.one(); 128]] {
        let mut a = cells[127];
        for (k, &d) in delta.iter().enumerate() {
            f.add(&mut a, &f.mulf(&d, &t[k]));
        }
        let proof = DualPacking128Proof { u, a };
        let rows = super::reconstruct(&basis, &claim, &proof, &delta, &f);
        assert_eq!(
            residuals(&rows, &pack(&bits), &aux, &cells, &f),
            [f.zero(); 2]
        );
    }
}
#[test]
fn lean_inconsistent_square_cell_regression() {
    // PippoDreams DualPacking/AuditCases.lean: this false statement accepts at
    // one particular challenge without requiring b=r^2. Do not strengthen it.
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let claim = BitLinearClaim {
        weights: vec![f.zero()],
        auxiliary_count: 0,
        rhs: AffineClaim {
            constant: f.one(),
            terms: vec![],
        },
    };
    let mut cells = [f.zero(); 129];
    cells[128] = basis.dual(0);
    let proof = DualPacking128Proof {
        u: [f.zero(); 128],
        a: f.zero(),
    };
    let mut delta = [f.zero(); 128];
    delta[0] = f.one();
    super::validate_traces(&basis, &proof.u).unwrap();
    let rows = super::reconstruct(&basis, &claim, &proof, &delta, &f);
    assert_eq!(
        residuals(&rows, &[f.zero()], &[], &cells, &f),
        [f.zero(); 2]
    );
    let zero_rows = super::reconstruct(&basis, &claim, &proof, &[f.zero(); 128], &f);
    assert_ne!(
        residuals(&zero_rows, &[f.zero()], &[], &cells, &f),
        [f.zero(); 2]
    );
}
#[test]
fn second_equation_alone_allows_an_adaptive_false_target() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let claim = BitLinearClaim {
        weights: vec![f.zero()],
        auxiliary_count: 0,
        rhs: AffineClaim {
            constant: f.one(),
            terms: vec![],
        },
    };
    let mut delta = [f.zero(); 128];
    delta[0] = f.one();
    let mut a = basis.dual(0);
    for _ in 0..127 {
        a = f.mulf(&a, &a);
    } // sqrt(eta), chosen after delta.
    let proof = DualPacking128Proof {
        u: [f.zero(); 128],
        a,
    };
    let rows = super::reconstruct(&basis, &claim, &proof, &delta, &f);
    let errors = residuals(&rows, &[f.zero()], &[], &[f.zero(); 129], &f);
    assert!(!f.is_zero(&errors[0]));
    assert!(f.is_zero(&errors[1]));
}
#[test]
fn complete_u_precedes_delta_and_a_is_bound_afterward() {
    let f = F::new();
    let (claim, _, _, _, _) = case(7, 11);
    let mut a = Transcript::new(b"order");
    let mut b = a.clone();
    super::transcript::begin(&claim, b"source", &mut a, &f);
    super::transcript::begin(&claim, b"source", &mut b, &f);
    let u = [f.zero(); 128];
    let mut other = u;
    other[127] = f.one();
    let da = super::transcript::challenge(&u, &mut a, &f);
    let db = super::transcript::challenge(&other, &mut b, &f);
    assert_ne!(da, db);
    assert_ne!(da[1], f.mulf(&da[0], &da[0]));
    let mut other_a = a.clone();
    super::transcript::finish(f.zero(), &mut a, &f);
    super::transcript::finish(f.one(), &mut other_a, &f);
    assert_ne!(a.bytes(32), other_a.bytes(32));
}
#[test]
fn masked_reduction_and_verifier_transcript_agree() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    for n in [0, 1, 2, 7, 8, 127, 128, 129, 255, 257, 513] {
        let (claim, bits, aux, masks, cells) = case(n, 100 + n as u64);
        let mut pt = Transcript::new(b"roundtrip");
        let mut vt = pt.clone();
        let (proof, rows) =
            prover::reduce(&basis, &claim, &bits, &aux, masks, b"source", &mut pt, &f).unwrap();
        assert!(proof.u.iter().all(|&u| !basis.trace_bit(u)));
        assert_eq!(
            verifier::reduce(&basis, &claim, &proof, b"source", &mut vt, &f).unwrap(),
            rows
        );
        assert_eq!(pt.bytes(32), vt.bytes(32));
        assert_eq!(
            residuals(&rows, &pack(&bits), &aux, &cells, &f),
            [f.zero(); 2]
        );
        let mut bytes = vec![];
        proof.write_to_buf(&mut bytes);
        assert_eq!(bytes.len(), 2064);
        assert_eq!(DualPacking128Proof::from_bytes(&bytes).unwrap(), proof);
    }
}
#[test]
fn changed_messages_context_claims_and_auxiliaries_fail() {
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let (claim, bits, aux, masks, cells) = case(129, 7);
    let packed = pack(&bits);
    let start = Transcript::new(b"binding");
    let (proof, _) = prover::reduce(
        &basis,
        &claim,
        &bits,
        &aux,
        masks,
        b"source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    for j in 0..128 {
        let mut bad = proof.clone();
        // Tr(1)=0: exercise authentication, not just trace rejection.
        f.add(&mut bad.u[j], &f.one());
        let rows =
            verifier::reduce(&basis, &claim, &bad, b"source", &mut start.clone(), &f).unwrap();
        assert_ne!(residuals(&rows, &packed, &aux, &cells, &f), [f.zero(); 2]);
    }
    let mut bad = proof.clone();
    f.add(&mut bad.a, &f.one());
    let changed_a =
        verifier::reduce(&basis, &claim, &bad, b"source", &mut start.clone(), &f).unwrap();
    assert_ne!(
        residuals(&changed_a, &packed, &aux, &cells, &f),
        [f.zero(); 2]
    );
    let different_context = verifier::reduce(
        &basis,
        &claim,
        &proof,
        b"other source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    assert_ne!(
        residuals(&different_context, &packed, &aux, &cells, &f),
        [f.zero(); 2]
    );
    let mut other = claim.clone();
    f.add(&mut other.rhs.constant, &f.one());
    let different_target =
        verifier::reduce(&basis, &other, &proof, b"source", &mut start.clone(), &f).unwrap();
    assert_ne!(
        residuals(&different_target, &packed, &aux, &cells, &f),
        [f.zero(); 2]
    );
    let original =
        verifier::reduce(&basis, &claim, &proof, b"source", &mut start.clone(), &f).unwrap();
    let mut other_aux = aux;
    f.add(&mut other_aux[0], &f.one());
    assert_ne!(
        residuals(&original, &packed, &other_aux, &cells, &f),
        [f.zero(); 2]
    );
}
#[test]
fn malformed_shapes_and_nonzero_traces_leave_transcript_unchanged() {
    for len in [0, 112, 2032, 2048, 2063, 2065] {
        assert!(DualPacking128Proof::from_bytes(&vec![0; len]).is_err());
    }
    let f = F::new();
    let basis = PolynomialBasis128::new(&f);
    let (mut claim, bits, aux, masks, _) = case(7, 9);
    let start = Transcript::new(b"shape");
    let mut bad_claim_transcript = start.clone();
    claim.rhs.terms[0].0 = 3;
    assert!(prover::reduce(
        &basis,
        &claim,
        &bits,
        &aux,
        masks,
        b"",
        &mut bad_claim_transcript,
        &f
    )
    .is_err());
    assert_eq!(bad_claim_transcript.bytes(32), start.clone().bytes(32));
    claim.rhs.terms[0].0 = 0;
    let mut proof = DualPacking128Proof {
        u: [f.zero(); 128],
        a: f.zero(),
    };
    proof.u[127] = basis.dual(0);
    let mut bad_trace_transcript = start.clone();
    assert!(verifier::reduce(&basis, &claim, &proof, b"", &mut bad_trace_transcript, &f).is_err());
    assert_eq!(bad_trace_transcript.bytes(32), start.clone().bytes(32));
    let (_, _, _, other_masks, _) = case(7, 9);
    let mut bad_aux_transcript = start.clone();
    assert!(prover::reduce(
        &basis,
        &claim,
        &bits,
        &aux[..2],
        other_masks,
        b"",
        &mut bad_aux_transcript,
        &f
    )
    .is_err());
    assert_eq!(bad_aux_transcript.bytes(32), start.clone().bytes(32));
    assert!(unpack(&[], 1).is_err());
    assert_eq!(PackedBits::from_le_bytes(&[255], 1).unwrap().word128(0), 1);
}
