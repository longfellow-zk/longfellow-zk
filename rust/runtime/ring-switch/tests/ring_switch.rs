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

//! Independent polynomial-coordinate, trace, transcript and malformed-proof checks.
use super::{
    field::{
        dual_coordinate_numerators, frobenius, pack, select_bit, trace, unpack, PolynomialBasis128,
    },
    prover::{self, RingMaskValues},
    verifier, AffineClaim, BitLinearClaim, RingSwitch128Proof, RING_MASK_CELLS, RING_MESSAGES,
};
use crate::{
    core::{algebra::AlgebraicField, bits::PackedBits},
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};

#[test]
fn polynomial_coordinates_and_trace_dual_basis() {
    let f = Gf2_128Field::new();
    let basis = PolynomialBasis128::new(&f);
    for j in 0..128 {
        let word = Gf2_128::from(1u128 << j);
        let bits = unpack(&[word], 128).unwrap();
        assert_eq!(bits.word128(0), 1u128 << j);
        assert_eq!(pack(&bits), vec![word]);
        for k in 0..128 {
            assert_eq!(
                trace(f.mulf(&basis.dual(j), &Gf2_128::from(1u128 << k)), &f),
                if j == k { f.one() } else { f.zero() },
                "dual ({j},{k})"
            );
        }
    }
}
#[test]
fn transposed_dual_coordinates_match_trace_pairing() {
    let f = Gf2_128Field::new();
    let basis = PolynomialBasis128::new(&f);
    // Across these permutations, every (coefficient index, bit index) occurs.
    for rotation in 0..128 {
        let row =
            std::array::from_fn::<_, 128, _>(|j| Gf2_128::from(1u128 << ((j + rotation) % 128)));
        let numerators = dual_coordinate_numerators(&row);
        for (h, numerator) in numerators.iter().enumerate() {
            assert_eq!(
                f.mulf(&basis.dual(127), numerator),
                basis.dual((h + 128 - rotation) % 128),
                "rotation={rotation}, coordinate={h}",
            );
        }
    }
    let mut rng = DeterministicRng::new(519);
    for n in [0, 1, 7, 63, 127, 128] {
        let row = (0..n)
            .map(|_| Gf2_128::from(rng.u128()))
            .collect::<Vec<_>>();
        let numerators = dual_coordinate_numerators(&row);
        for (h, numerator) in numerators.iter().enumerate() {
            let mut direct = f.zero();
            for (j, coefficient) in row.iter().enumerate() {
                f.add(&mut direct, &select_bit(basis.dual(j), coefficient.bit(h)));
            }
            assert_eq!(
                f.mulf(&basis.dual(127), numerator),
                direct,
                "n={n}, coordinate={h}"
            );
        }
    }
}

#[test]
fn compressed_components_match_direct_linear_forms_and_original_bit_claim() {
    let f = Gf2_128Field::new();
    let basis = PolynomialBasis128::new(&f);
    for n in [0, 1, 7, 127, 128, 129, 257, 513] {
        let (claim, bits, aux, _, _) = case(n, 19 + n as u64);
        let packed = pack(&bits);
        let components = prover::components(&basis, &claim.weights, &bits, &f);
        let mut powers = claim.weights.clone();
        for t in 1..128 {
            let mut value = f.zero();
            for (index, r) in powers.iter_mut().enumerate() {
                *r = f.mulf(r, r);
                let coefficient = f.mulf(&basis.dual(index % 128), r);
                f.add(&mut value, &f.mulf(&coefficient, &packed[index / 128]));
            }
            assert_eq!(components[127 - t], value, "n={n}, component={}", 128 - t);
        }
        let mut value = f.zero();
        for (index, &r) in claim.weights.iter().enumerate() {
            let coefficient = f.mulf(&basis.dual(index % 128), &r);
            f.add(&mut value, &f.mulf(&coefficient, &packed[index / 128]));
        }
        for (index, &v) in components.iter().enumerate() {
            f.add(&mut value, &frobenius(v, index + 1, &f));
        }
        assert_eq!(value, claim.rhs.evaluate(&aux, &f).unwrap(), "n={n}");
    }
}

#[test]
fn transposed_reconstruction_matches_dense_public_coefficients() {
    let f = Gf2_128Field::new();
    let basis = PolynomialBasis128::new(&f);
    let mut rng = DeterministicRng::new(815);
    let gamma = std::array::from_fn(|_| Gf2_128::from(rng.u128()));
    let beta = Gf2_128::from(rng.u128());
    let proof = RingSwitch128Proof {
        messages: std::array::from_fn(|_| Gf2_128::from(rng.u128())),
    };
    for n in [0, 1, 127, 128, 129, 257, 513] {
        let (claim, _, _, _, _) = case(n, 27 + n as u64);
        let result = super::reconstruct(&basis, &claim, &proof, beta, &gamma, &f);
        let expected = claim
            .weights
            .chunks(128)
            .map(|row| {
                let mut value = f.zero();
                for (j, &r) in row.iter().enumerate() {
                    let mut x = r;
                    let mut psi = r;
                    for t in 1..128 {
                        x = f.mulf(&x, &x);
                        f.add(&mut psi, &f.mulf(&gamma[127 - t], &x));
                    }
                    f.add(&mut value, &f.mulf(&basis.dual(j), &psi));
                }
                value
            })
            .collect::<Vec<_>>();
        assert_eq!(result.weights, expected, "n={n}");
    }
}
#[test]
fn entire_response_precedes_independent_batching_challenges() {
    let f = Gf2_128Field::new();
    let (claim, _, _, _, _) = case(7, 11);
    let mut a = Transcript::new(b"flat order");
    let mut b = a.clone();
    let beta = super::transcript::begin(&claim, b"", &mut a, &f);
    assert_eq!(beta, super::transcript::begin(&claim, b"", &mut b, &f));
    let proof = RingSwitch128Proof {
        messages: [f.zero(); RING_MESSAGES],
    };
    let mut bad = proof.clone();
    bad.messages[RING_MESSAGES - 1] = f.one();
    let ga = super::transcript::batch(&proof, &mut a, &f);
    let gb = super::transcript::batch(&bad, &mut b, &f);
    assert_ne!(ga[0], gb[0]);
    assert_ne!(ga[1], f.mulf(&ga[0], &ga[0]));
    for (index, alpha) in super::inverse_twists(beta, &f).into_iter().enumerate() {
        assert_eq!(frobenius(alpha, index + 1, &f), beta);
    }
}
fn case(
    n: usize,
    seed: u64,
) -> (
    BitLinearClaim,
    PackedBits,
    Vec<Gf2_128>,
    RingMaskValues,
    [Gf2_128; RING_MASK_CELLS],
) {
    let f = Gf2_128Field::new();
    let mut rng = DeterministicRng::new(seed);
    let bits: PackedBits = (0..n).map(|_| rng.u128() & 1 != 0).collect();
    let weights: Vec<_> = (0..n).map(|_| Gf2_128::from(rng.u128())).collect();
    let auxiliary: Vec<_> = (0..3).map(|_| Gf2_128::from(rng.u128())).collect();
    let terms: Vec<_> = (0..3).map(|i| (i, Gf2_128::from(rng.u128()))).collect();
    let mut constant = f.zero();
    for (i, a) in weights.iter().enumerate() {
        f.add(&mut constant, &select_bit(*a, bits.get(i)));
    }
    for &(i, a) in &terms {
        f.add(&mut constant, &f.mulf(&a, &auxiliary[i]));
    }
    let claim = BitLinearClaim {
        weights,
        auxiliary_count: 3,
        rhs: AffineClaim { constant, terms },
    };
    let masks = RingMaskValues::sample(&mut rng, &f);
    let cells = masks.cells();
    (claim, bits, auxiliary, masks, cells)
}

#[test]
fn masked_reduction_and_verifier_transcript_agree() {
    let f = Gf2_128Field::new();
    for n in [0, 1, 2, 7, 8, 127, 128, 129, 255, 257, 513] {
        let (claim, bits, auxiliary, masks, cells) = case(n, 100 + n as u64);
        let mut pt = Transcript::new(b"standalone ring test");
        let mut vt = pt.clone();
        let (proof, output) = prover::reduce(
            &PolynomialBasis128::new(&f),
            &claim,
            &bits,
            masks,
            b"source",
            &mut pt,
            &f,
        )
        .unwrap();
        let expected = verifier::reduce(
            &PolynomialBasis128::new(&f),
            &claim,
            &proof,
            b"source",
            &mut vt,
            &f,
        )
        .unwrap();
        assert_eq!(output, expected);
        assert_eq!(pt.bytes(32), vt.bytes(32));
        assert_eq!(
            output
                .residual(&pack(&bits), &auxiliary, &cells, &f)
                .unwrap(),
            f.zero()
        );
        let mut bytes = Vec::new();
        proof.write_to_buf(&mut bytes);
        assert_eq!(bytes.len(), 2032);
        assert_eq!(RingSwitch128Proof::from_bytes(&bytes).unwrap(), proof);
    }
}

#[test]
fn incorrect_checksum_has_exact_randomized_error() {
    let f = Gf2_128Field::new();
    let (mut claim, bits, auxiliary, masks, mut cells) = case(193, 5);
    let delta = Gf2_128::from(123);
    let checksum_error = Gf2_128::from(456);
    f.add(&mut claim.rhs.constant, &delta);
    f.add(&mut cells[RING_MESSAGES], &checksum_error);
    let (_, output) = prover::reduce(
        &PolynomialBasis128::new(&f),
        &claim,
        &bits,
        masks,
        b"source",
        &mut Transcript::new(b"bad checksum"),
        &f,
    )
    .unwrap();
    let actual = output
        .residual(&pack(&bits), &auxiliary, &cells, &f)
        .unwrap();
    assert_eq!(
        actual,
        f.addf(&delta, &f.mulf(&output.checksum_weight, &checksum_error))
    );
    assert!(!f.is_zero(&actual));
}

#[test]
fn changed_messages_context_auxiliaries_and_claims_fail() {
    let f = Gf2_128Field::new();
    let (claim, bits, auxiliary, masks, cells) = case(129, 7);
    let packed = pack(&bits);
    let start = Transcript::new(b"binding");
    let (proof, _) = prover::reduce(
        &PolynomialBasis128::new(&f),
        &claim,
        &bits,
        masks,
        b"source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    for j in 0..RING_MESSAGES {
        let mut bad = proof.clone();
        f.add(&mut bad.messages[j], &f.one());
        let out = verifier::reduce(
            &PolynomialBasis128::new(&f),
            &claim,
            &bad,
            b"source",
            &mut start.clone(),
            &f,
        )
        .unwrap();
        assert!(!f.is_zero(&out.residual(&packed, &auxiliary, &cells, &f).unwrap()));
    }
    let context_result = verifier::reduce(
        &PolynomialBasis128::new(&f),
        &claim,
        &proof,
        b"other source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    assert!(!f.is_zero(
        &context_result
            .residual(&packed, &auxiliary, &cells, &f)
            .unwrap()
    ));
    let mut other_claim = claim.clone();
    f.add(&mut other_claim.rhs.constant, &f.one());
    let claim_result = verifier::reduce(
        &PolynomialBasis128::new(&f),
        &other_claim,
        &proof,
        b"source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    assert!(!f.is_zero(
        &claim_result
            .residual(&packed, &auxiliary, &cells, &f)
            .unwrap()
    ));
    let auxiliary_result = verifier::reduce(
        &PolynomialBasis128::new(&f),
        &claim,
        &proof,
        b"source",
        &mut start.clone(),
        &f,
    )
    .unwrap();
    let mut bad_auxiliary = auxiliary;
    f.add(&mut bad_auxiliary[0], &f.one());
    assert!(!f.is_zero(
        &auxiliary_result
            .residual(&packed, &bad_auxiliary, &cells, &f)
            .unwrap()
    ));
}

#[test]
fn malformed_shapes_reject_without_changing_transcript() {
    for len in [0, 112, 2031, 2033, 2048] {
        assert!(RingSwitch128Proof::from_bytes(&vec![0; len]).is_err());
    }
    let f = Gf2_128Field::new();
    let (mut claim, bits, _, masks, _) = case(7, 9);
    claim.rhs.terms[0].0 = 3;
    let original = Transcript::new(b"shape");
    let mut ts = original.clone();
    assert!(prover::reduce(
        &PolynomialBasis128::new(&f),
        &claim,
        &bits,
        masks,
        b"",
        &mut ts,
        &f
    )
    .is_err());
    assert_eq!(ts.bytes(32), original.clone().bytes(32));
    assert!(unpack(&[], 1).is_err());
    let bit = PackedBits::from_le_bytes(&[255], 1).unwrap();
    assert_eq!(bit.word128(0), 1);
}
