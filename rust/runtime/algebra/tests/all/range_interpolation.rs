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

use std::ops::Range;

use crate::{
    core::algebra::{AlgebraicField, SupportsU64Conversions},
    runtime::algebra::{
        fp2::Fp2Field,
        gf2_128::{Gf2_128, Gf2_128RuntimeField},
        p256::P256Field,
        q256::Q256Field,
        range_interpolation::{
            interpolate_range, BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            ScalarInterpolatorFactory,
        },
        subfield_v1::BinarySubfield,
        InterpolationPlan, RangeInterpolatorFactory, RuntimeField, SupportsFFT,
    },
};

// SplitMix64 gives reproducible random coefficients without external test state.
fn random_word(index: usize) -> u64 {
    let mut value = (index as u64).wrapping_add(0x9e3779b97f4a7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
    value ^ (value >> 31)
}

fn evaluate<F: AlgebraicField>(f: &F, coefficients: &[F::E], x: &F::E) -> F::E {
    coefficients
        .iter()
        .rev()
        .fold(f.zero(), |acc, c| f.addf(&f.mulf(&acc, x), c))
}

fn case<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    f: &F,
    domain: &D,
    source: Range<usize>,
    destination: Range<usize>,
    coefficient: impl Fn(usize) -> F::E,
) {
    assert!(domain.can_interpolate(source.clone(), destination.clone()));
    let plan = domain.make_range(source.clone(), destination.clone());
    // Reuse one immutable plan for three unrelated rows, each with its own output.
    for row in 0..3 {
        let coefficients: Vec<_> = (0..source.len())
            .map(|i| coefficient(i + row * 97))
            .collect();
        assert_ne!(
            coefficients.last(),
            Some(&f.zero()),
            "test must exercise exact degree k-1"
        );
        let values: Vec<_> = source
            .clone()
            .map(|i| evaluate(f, &coefficients, &domain.point(i)))
            .collect();
        let saved = values.clone();
        let expected: Vec<_> = destination
            .clone()
            .map(|i| evaluate(f, &coefficients, &domain.point(i)))
            .collect();
        let actual = plan.apply(&values);
        assert_eq!(
            actual, expected,
            "source={source:?}, destination={destination:?}, row={row}"
        );
        assert_eq!(values, saved);
        // The allocating wrapper and &factory forwarding agree.
        if row == 0 {
            assert_eq!(
                interpolate_range(source.start, &values, destination.clone(), &domain),
                expected
            );
        }
    }
}

fn exercise<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    f: &F,
    domain: &D,
    coefficient: impl Fn(usize) -> F::E,
    limit: usize,
) {
    for k in [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65] {
        for a in [0, 1, 3, 15, 127] {
            let source = a..a + k;
            let destinations = [
                0..0,
                limit..limit,
                0..1,
                a..a + k,
                a..a + k / 2,
                a.saturating_sub(3)..a + 3,
                a + k - 1..a + k + 4,
                a + k..a + 3 * k + 3,
                2 * k + 200..4 * k + 201,
                limit - 3..limit,
            ];
            for destination in destinations {
                case(f, domain, source.clone(), destination, &coefficient);
            }
        }
    }
    for value in [f.zero(), f.one()] {
        let source = vec![value.clone(); 17];
        assert_eq!(
            interpolate_range(3, &source, 0..100, domain),
            vec![value; 100]
        );
    }
}

// Independent Lagrange formula: no production weights, FFTs, or Newton helpers.
fn lagrange<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    f: &F,
    domain: &D,
    values: &[F::E],
    begin: usize,
    index: usize,
) -> F::E {
    let x = domain.point(index);
    let mut result = f.zero();
    for (i, v) in values.iter().enumerate() {
        let xi = domain.point(begin + i);
        let mut numerator = f.one();
        let mut denominator = f.one();
        for j in 0..values.len() {
            if j != i {
                let xj = domain.point(begin + j);
                f.mul(&mut numerator, &f.subf(&x, &xj));
                f.mul(&mut denominator, &f.subf(&xi, &xj));
            }
        }
        f.add(
            &mut result,
            &f.mulf(v, &f.mulf(&numerator, &f.invert(&denominator))),
        );
    }
    result
}

fn arbitrary_values<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    f: &F,
    domain: &D,
    sample: impl Fn(usize) -> F::E,
) {
    for (source, destination) in [(1..5, 0..11), (7..16, 3..25), (31..33, 0..5)] {
        let values: Vec<_> = source.clone().map(&sample).collect();
        let actual = interpolate_range(source.start, &values, destination.clone(), domain);
        let expected: Vec<_> = destination
            .map(|i| lagrange(f, domain, &values, source.start, i))
            .collect();
        assert_eq!(actual, expected);
    }
}

fn invalid_ranges<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    f: &F,
    domain: &D,
    limit: usize,
) {
    for (source, destination) in [
        (0..0, 0..0),
        (Range { start: 4, end: 3 }, 0..1),
        (0..1, Range { start: 3, end: 2 }),
        (limit..limit + 1, 0..1),
        (0..1, limit..limit + 1),
        (usize::MAX - 1..usize::MAX, 0..1),
    ] {
        assert!(!domain.can_interpolate(source.clone(), destination.clone()));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || domain.make_range(source.clone(), destination.clone())
        ))
        .is_err());
    }
    let plan = domain.make_range(2..5, 0..7);
    for input in [2, 4] {
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            plan.apply(&vec![f.one(); input]);
        }))
        .is_err());
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| domain.point(limit))).is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| interpolate_range(
            usize::MAX,
            &[f.one()],
            0..1,
            domain
        )))
        .is_err()
    );
}

fn prefix_suffix_consistency<
    const W: usize,
    F: RuntimeField<W>,
    D: RangeInterpolatorFactory<W, F>,
>(
    domain: &D,
    sample: impl Fn(usize) -> F::E,
) {
    for k in [1, 2, 3, 7, 8, 9, 31, 32, 33, 63, 64, 65] {
        let m = 4 * k + 3;
        let source: Vec<_> = (0..k).map(&sample).collect();
        let full = interpolate_range(0, &source, 0..m, domain);
        assert_eq!(full[..k], source);
        for start in [k, k + 1, m / 2, m] {
            assert_eq!(
                interpolate_range(0, &source, start..m, domain),
                full[start..]
            );
        }
    }
}

#[test]
fn quadratic_extension_fft_range_interpolation() {
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let factory =
        QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    let coefficient = |i| f.u64_to_element(random_word(i));
    exercise(&f, &factory, coefficient, 1 << 20);
    arbitrary_values(&f, &factory, coefficient);
    prefix_suffix_consistency(&factory, coefficient);
    // High indices must not allocate or compute across the gap, or overflow
    // begin+lag arithmetic while preparing convolution kernels.
    case(
        &f,
        &factory,
        usize::MAX - 100..usize::MAX - 91,
        usize::MAX - 4..usize::MAX,
        coefficient,
    );
    let small = QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), 16);
    assert!(!small.can_interpolate(0..17, 20..25));
    assert!(small.can_interpolate(0..17, 1..5));
    let plan = factory.make_range(4..7, 0..3);
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| plan.apply(&[f.one(); 2])))
            .is_err()
    );
}

#[test]
fn binary_range_interpolation() {
    let f = Gf2_128RuntimeField::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let factory = BinaryInterpolatorFactory::new(&f, &sf);
    let coefficient = |i| {
        Gf2_128::from(u128::from(random_word(2 * i)) | (u128::from(random_word(2 * i + 1)) << 64))
    };
    exercise(&f, &factory, coefficient, 1 << 16);
    arbitrary_values(&f, &factory, coefficient);
    prefix_suffix_consistency(&factory, coefficient);
    invalid_ranges(&f, &factory, 1 << 16);
    for k in 1..17 {
        for a in 0..33 {
            case(&f, &factory, a..a + k, 29..47, coefficient);
        }
    }
    for r in 2..16 {
        case(&f, &factory, (1 << r) - 1..(1 << r) + 1, 3..19, coefficient);
    }
    for (source, destination) in [
        (512..1042, 512..4608),
        (8704..9234, 4093..12291),
        (32767..32769, 3..19),
        (65533..65536, 65525..65536),
    ] {
        case(&f, &factory, source, destination, coefficient);
    }
}

#[test]
fn scalar_range_interpolation() {
    let f = Q256Field::new();
    let factory = ScalarInterpolatorFactory::<4, _>::new(&f, 2048);
    let coefficient = |i| f.u64_to_element(random_word(i));
    exercise(&f, &factory, coefficient, 2048);
    arbitrary_values(&f, &factory, coefficient);
    invalid_ranges(&f, &factory, 2048);
}

#[cfg(feature = "experimental")]
#[test]
fn crt_range_interpolation() {
    use crate::runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
    };
    let f = RuntimeFp24Ext6::new();
    let factory = CrtInterpolatorFactory;
    let coefficient = |i| {
        f.from_coefficients(std::array::from_fn(|j| {
            (random_word(6 * i + j) % 8_380_417) as u32
        }))
    };
    exercise(&f, &factory, coefficient, 8_380_417);
    arbitrary_values(&f, &factory, coefficient);
    prefix_suffix_consistency(&factory, coefficient);
    invalid_ranges(&f, &factory, 8_380_417);
    for source in [1..5, 127..160] {
        let destination = 0..200;
        let values: Vec<_> = source
            .clone()
            .map(|i| f.u64_to_element((i * i + 1) as u64))
            .collect();
        let plan = factory.make_range(source.clone(), destination.clone());
        let actual = plan.apply(&values);
        let expected: Vec<_> = destination
            .map(|i| evaluate(&f, &[f.one(), f.zero(), f.one()], &factory.point(i)))
            .collect();
        assert_eq!(actual, expected);
    }
    let q = u128::from(crate::core::algebra::fp24::Q - 1);
    let bound = ((18_446_744_072_195_407_873u128 - 1) / (q * q)) as usize;
    assert!(factory.can_interpolate(0..bound, bound..bound + 1));
    assert!(!factory.can_interpolate(0..bound + 1, bound + 1..bound + 2));
}

#[test]
fn binary_range_interpolation_with_non_cantor_basis() {
    let f = Gf2_128RuntimeField::new();
    let basis: Vec<_> = (0..8).map(|i| 1u128 << i).collect();
    let sf = BinarySubfield::new(&basis);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let sample = |i| Gf2_128::from(u128::from(random_word(i)));
    arbitrary_values(&f, &domain, sample);
    for a in [0, 1, 3, 15, 31, 127] {
        for k in [1, 3, 7, 8, 9, 15, 16, 17] {
            case(&f, &domain, a..a + k, 113..174, sample);
        }
    }
}

#[test]
fn quadratic_extension_fft_range_capacity_rejects_invalid_fft_root_orders() {
    let field = P256Field::new();
    let extension = Fp2Field::new(&field);
    for order in [0, 3, 12] {
        let factory = QuadraticExtensionFftInterpolatorFactory::new(
            &field,
            &extension,
            extension.omega(),
            order,
        );
        assert!(!factory.can_interpolate(0..2, 2..5));
        // Copying and constant interpolation do not use an FFT root.
        assert!(factory.can_interpolate(0..2, 0..1));
        assert!(factory.can_interpolate(5..6, 0..15));
        let result = factory.make_range(5..6, 0..15).apply(&[field.one()]);
        assert_eq!(result, vec![field.one(); 15]);
    }
}

/// Check the backend contract independently of any proof protocol. Include the
/// end of each finite table so a wrapping point map cannot pass a prefix check.
fn assert_distinct_points<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    _field: &F,
    domain: &D,
    ranges: impl IntoIterator<Item = Range<usize>>,
) {
    let indices: std::collections::BTreeSet<_> = ranges.into_iter().flatten().collect();
    let mut points = std::collections::HashSet::new();
    for index in indices {
        assert!(
            points.insert(domain.point(index)),
            "repeated point at {index}"
        );
    }
}

#[test]
fn interpolation_backend_points_are_distinct() {
    let prime = P256Field::new();
    let quadratic = Fp2Field::new(&prime);
    let fft = QuadraticExtensionFftInterpolatorFactory::new(
        &prime,
        &quadratic,
        quadratic.omega(),
        quadratic.omega_order(),
    );
    assert_distinct_points(&prime, &fft, [0..8192, usize::MAX - 64..usize::MAX]);

    let scalar_field = Q256Field::new();
    let scalar = ScalarInterpolatorFactory::new(&scalar_field, 2048);
    assert_distinct_points(&scalar_field, &scalar, std::iter::once(0..2048));

    let binary_field = Gf2_128RuntimeField::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let binary = BinaryInterpolatorFactory::new(&binary_field, &subfield);
    assert_distinct_points(&binary_field, &binary, std::iter::once(0..1 << 16));
    let basis: Vec<_> = (0..8).map(|i| 1u128 << i).collect();
    let other_subfield = BinarySubfield::new(&basis);
    let other_binary = BinaryInterpolatorFactory::new(&binary_field, &other_subfield);
    assert_distinct_points(&binary_field, &other_binary, std::iter::once(0..256));

    #[cfg(feature = "experimental")]
    {
        use crate::runtime::algebra::{
            fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
        };
        let extension = RuntimeFp24Ext6::new();
        assert_distinct_points(
            &extension,
            &CrtInterpolatorFactory,
            [0..8192, 8_380_353..8_380_417],
        );
    }
}
