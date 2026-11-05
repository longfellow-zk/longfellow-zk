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
    core::algebra::AlgebraicField,
    runtime::algebra::{gf2_128::Gf2_128RuntimeField, subfield_v1::BinarySubfieldV1},
};

// Direct root products define the novel basis independently of either FFT.
fn evaluation_matrix(
    f: &Gf2_128RuntimeField,
    sf: &BinarySubfieldV1,
    size: usize,
    coset: usize,
) -> Vec<Vec<Gf2_128>> {
    let log = size.trailing_zeros() as usize;
    let vanishing = |j: usize, x: Gf2_128| {
        (0..1 << j).fold(f.one(), |value, i| {
            f.mulf(&value, &f.addf(&x, &sf.embed(i)))
        })
    };
    let inverses: Vec<_> = (0..log)
        .map(|j| f.invert(&vanishing(j, sf.embed(1 << j))))
        .collect();
    (0..size)
        .map(|i| {
            let x = sf.embed((i ^ coset) as u64);
            let factors: Vec<_> = (0..log)
                .map(|j| f.mulf(&vanishing(j, x), &inverses[j]))
                .collect();
            let mut row = vec![f.one(); size];
            for coefficient in 1..size {
                let bit = coefficient.trailing_zeros() as usize;
                row[coefficient] = f.mulf(&row[coefficient ^ (1 << bit)], &factors[bit]);
            }
            row
        })
        .collect()
}

#[test]
fn binary_mixed_transform_all_intervals_and_nonzero_tails() {
    let f = Gf2_128RuntimeField::new();
    let ordinary: Vec<_> = (0..8).map(|i| 1u128 << i).collect();
    for basis in [
        &crate::core::algebra::proto::GF2_16_BASIS_V1[..8],
        &ordinary,
    ] {
        let sf = BinarySubfieldV1::new(basis);
        let fft = Lch14::new(&f, sf.basis());
        for log in 0..=6 {
            let size = 1 << log;
            let matrix = evaluation_matrix(&f, &sf, size, 0);
            for count in 0..=size {
                for zero_tail in [false, true] {
                    let coefficients: Vec<_> = (0..size)
                        .map(|i| {
                            if zero_tail && i >= count {
                                f.zero()
                            } else {
                                Gf2_128::from(
                                    ((i as u128 + 1) * 0x123456789abcdef123456789u128)
                                        ^ ((count as u128) << 96),
                                )
                            }
                        })
                        .collect();
                    let evaluations: Vec<_> = matrix
                        .iter()
                        .map(|row| {
                            row.iter()
                                .zip(&coefficients)
                                .fold(f.zero(), |sum, (x, c)| f.addf(&sum, &f.mulf(x, c)))
                        })
                        .collect();
                    for start in 0..=size - count {
                        let plan = BinaryTransform::new(size, 0, start, count, &fft, &f);
                        let result = plan.apply(
                            &evaluations[start..start + count],
                            &coefficients[count..],
                            &fft,
                            &f,
                        );
                        assert_eq!(result.coefficients, coefficients, "binary coefficients: size={size}, start={start}, count={count}, zero_tail={zero_tail}");
                        assert_eq!(result.evaluations, evaluations, "binary evaluations: size={size}, start={start}, count={count}, zero_tail={zero_tail}");
                        let again = plan.apply(
                            &evaluations[start..start + count],
                            &coefficients[count..],
                            &fft,
                            &f,
                        );
                        assert_eq!(again.coefficients, coefficients);
                        assert_eq!(again.evaluations, evaluations);
                    }
                }
            }
        }
    }
}

#[test]
fn binary_mixed_transform_shifted_domains() {
    let f = Gf2_128RuntimeField::new();
    let ordinary: Vec<_> = (0..8).map(|i| 1u128 << i).collect();
    for basis in [
        &crate::core::algebra::proto::GF2_16_BASIS_V1[..8],
        &ordinary,
    ] {
        let sf = BinarySubfieldV1::new(basis);
        let fft = Lch14::new(&f, sf.basis());
        for log in 0..=5 {
            let size = 1 << log;
            for coset in [1, 7, 64, 127] {
                let matrix = evaluation_matrix(&f, &sf, size, coset);
                let coefficients: Vec<_> = (0..size)
                    .map(|i| Gf2_128::from((i as u128 + 1) * 0x123456789abcdef123456789u128))
                    .collect();
                let evaluations: Vec<_> = matrix
                    .iter()
                    .map(|row| {
                        row.iter()
                            .zip(&coefficients)
                            .fold(f.zero(), |sum, (a, b)| f.addf(&sum, &f.mulf(a, b)))
                    })
                    .collect();
                for count in 0..=size {
                    for start in 0..=size - count {
                        let plan = BinaryTransform::new(size, coset, start, count, &fft, &f);
                        let result = plan.apply(
                            &evaluations[start..start + count],
                            &coefficients[count..],
                            &fft,
                            &f,
                        );
                        assert_eq!(result.coefficients, coefficients, "shifted coefficients: size={size}, coset={coset}, start={start}, count={count}");
                        assert_eq!(result.evaluations, evaluations, "shifted evaluations: size={size}, coset={coset}, start={start}, count={count}");
                    }
                }
            }
        }
    }
}

#[test]
fn binary_domain_rejects_invalid_bases() {
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    assert!(std::panic::catch_unwind(|| BinaryInterpolatorFactory::new(&f, &[])).is_err());
    let one = Gf2_128::from(1);
    assert!(std::panic::catch_unwind(|| BinaryInterpolatorFactory::new(&f, &[one, one])).is_err());
}

#[test]
fn ambient_binary_domain_uses_native_coordinates_without_a_small_domain_limit() {
    let f = Gf2_128RuntimeField::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    assert_eq!(domain.basis.len(), 128);
    let point = |index: usize| {
        let mut value = 0u128;
        for bit in 0..usize::BITS {
            if index & (1usize << bit) != 0 {
                value ^= crate::core::algebra::CANTOR_BASIS_U128[bit as usize];
            }
        }
        Gf2_128::from(value)
    };
    for index in [0, 1, 0xffff, 0x10000, usize::MAX] {
        assert_eq!(domain.point(index), point(index));
    }
    let middle = 1usize << (usize::BITS - 1);
    assert!(!domain.can_interpolate(middle - 1..middle + 1, 0..2));
    let coefficients: Vec<_> = (0..7).map(|i| Gf2_128::from((i + 1) << 100)).collect();
    let value = |index| {
        let x = point(index);
        coefficients
            .iter()
            .rev()
            .fold(f.zero(), |sum, c| f.addf(c, &f.mulf(&sum, &x)))
    };
    for (source, destination) in [
        (3..10, 65536..65544),
        (usize::MAX - 15..usize::MAX - 8, 4..13),
        (5..12, usize::MAX - 9..usize::MAX),
    ] {
        assert!(domain.can_interpolate(source.clone(), destination.clone()));
        let samples: Vec<_> = source.clone().map(&value).collect();
        let actual = domain
            .make_range(source, destination.clone())
            .apply(&samples);
        let expected: Vec<_> = destination.map(&value).collect();
        assert_eq!(actual, expected);
    }
}
