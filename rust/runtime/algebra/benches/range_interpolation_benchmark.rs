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

//! Planning and row application are timed separately, including temporary
//! allocations. Prefix, shifted, and backward ranges use the same row sizes.
use std::{hint::black_box, ops::Range, time::Duration};

use criterion::{criterion_group, criterion_main, Criterion};
use longfellow_zk::{
    core::algebra::SupportsU64Conversions,
    runtime::algebra::{
        fp2::Fp2Field,
        gf2_128::{Gf2_128, Gf2_128RuntimeField},
        p256::P256Field,
        q256::Q256Field,
        range_interpolation::{
            BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            ScalarInterpolatorFactory,
        },
        subfield_v1::BinarySubfield,
        InterpolationPlan, RangeInterpolatorFactory, RuntimeField, SupportsFFT,
    },
};

fn benchmark<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    c: &mut Criterion,
    name: &str,
    domain: &D,
    source: Range<usize>,
    destination: Range<usize>,
    values: &[F::E],
) {
    let mut group = c.benchmark_group(name);
    group.bench_function("plan", |b| {
        b.iter(|| {
            black_box(domain.make_range(black_box(source.clone()), black_box(destination.clone())))
        })
    });
    let plan = domain.make_range(source, destination);
    group.bench_function("apply", |b| b.iter(|| plan.apply(black_box(values))));
    group.finish();
}

fn benchmark_ranges<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    c: &mut Criterion,
    name: &str,
    domain: &D,
    k: usize,
    destination: Range<usize>,
    values: &[F::E],
) {
    benchmark(
        c,
        &format!("{name}/prefix"),
        domain,
        0..k,
        destination.clone(),
        values,
    );
    benchmark(
        c,
        &format!("{name}/shifted"),
        domain,
        127..127 + k,
        destination.clone(),
        values,
    );
    benchmark(
        c,
        &format!("{name}/backward"),
        domain,
        destination.end..destination.end + k,
        0..destination.len(),
        values,
    );
}

fn all_backends(c: &mut Criterion) {
    {
        let f = P256Field::new();
        let f2 = Fp2Field::new(&f);
        let factory =
            QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
        let k = 416;
        let values: Vec<_> = (0..k)
            .map(|i| f.u64_to_element((i * i + 1) as u64))
            .collect();
        benchmark_ranges(
            c,
            "range/quadratic-extension-fft-v8",
            &factory,
            k,
            416..3328,
            &values,
        );
    }
    {
        let f = Gf2_128RuntimeField::new();
        let sf = BinarySubfield::new(&longfellow_zk::core::algebra::proto::GF2_16_BASIS_V1);
        let factory = BinaryInterpolatorFactory::new(&f, &sf);
        let k = 512;
        let values: Vec<_> = (0..k)
            .map(|i| Gf2_128::from((i as u128 + 1) * 0x123456789abcdef123456789u128))
            .collect();
        benchmark_ranges(c, "range/binary-v8", &factory, k, 4096..7680, &values);
    }
    {
        let f = Q256Field::new();
        let factory = ScalarInterpolatorFactory::<4, _>::new(&f, 1024);
        let values: Vec<_> = (0..32).map(|i| f.u64_to_element(i * i + 1)).collect();
        benchmark(c, "range/scalar", &factory, 3..35, 128..256, &values);
    }
    #[cfg(feature = "experimental")]
    {
        use longfellow_zk::runtime::algebra::{
            fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
        };
        let f = RuntimeFp24Ext6::new();
        let factory = CrtInterpolatorFactory;
        let k = 992;
        let values: Vec<_> = (0..k)
            .map(|i| f.from_coefficients(std::array::from_fn(|j| (i * i + 17 * j + 1) as u32)))
            .collect();
        benchmark_ranges(c, "range/crt-mldsa", &factory, k, 992..4960, &values);
        let base_values: Vec<_> = (0..k)
            .map(|i| f.u64_to_element((i * i + 1) as u64))
            .collect();
        let plan = factory.make_range(0..k, 992..4960);
        let mut group = c.benchmark_group("range/crt-mldsa/base-inputs");
        group.bench_function("apply", |b| b.iter(|| plan.apply(black_box(&base_values))));
        group.finish();
    }
}
fn binary_ranges(c: &mut Criterion) {
    let f = Gf2_128RuntimeField::new();
    let sf = BinarySubfield::new(&longfellow_zk::core::algebra::proto::GF2_16_BASIS_V1);
    let factory = BinaryInterpolatorFactory::new(&f, &sf);
    for (name, source, destination) in [
        ("easy-control", 0..512, 512..4096),
        ("v8-h", 512..1042, 512..4096),
        ("v8-h-wide", 512..1042, 0..32768),
        ("unbalanced", 511..1023, 512..4608),
        ("two-large-pieces", 257..787, 512..4608),
        ("small", 127..159, 0..512),
        ("high-boundary", 32767..32769, 3..19),
    ] {
        let values: Vec<_> = (0..source.len())
            .map(|i| Gf2_128::from((i as u128 + 1) * 0x123456789abcdef123456789u128))
            .collect();
        benchmark(
            c,
            &format!("range/binary/{name}"),
            &factory,
            source,
            destination,
            &values,
        );
    }
}
criterion_group! {
    name=benches;
    config=Criterion::default().warm_up_time(Duration::from_millis(100)).measurement_time(Duration::from_millis(400)).sample_size(10);
    targets=all_backends, binary_ranges
}
criterion_main!(benches);
