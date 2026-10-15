// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use circuits_experimental::mldsa::algebra::{
    CompileFp24Ext6, RuntimeFp24Ext6, RuntimeFp24Subfield, BETA, Q,
};
use core_algebra::{AlgebraicField, SerializableField, SupportsU64Conversions};
use runtime_algebra::{
    field::RuntimeSerializableField, Interpolator, InterpolatorFactory, Subfield,
};

#[test]
fn compile_and_runtime_fields_agree() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let a_coefficients = [Q - 1, 2, 3, 4, 5, 6];
    let b_coefficients = [7, 8, 9, 10, 11, 12];

    let mut compile_product = compile.from_coefficients(a_coefficients);
    compile.mul(
        &mut compile_product,
        &compile.from_coefficients(b_coefficients),
    );
    let mut runtime_product = runtime.from_coefficients(a_coefficients);
    runtime.mul(
        &mut runtime_product,
        &runtime.from_coefficients(b_coefficients),
    );

    assert_eq!(
        compile.to_bytes(&compile_product),
        runtime.to_bytes(&runtime_product)
    );
    // x^6 = beta in the defining quotient ring.
    let mut x = compile.from_coefficients([0, 1, 0, 0, 0, 0]);
    for _ in 1..6 {
        x = compile.mulf(&x, &compile.from_coefficients([0, 1, 0, 0, 0, 0]));
    }
    assert_eq!(x, compile.u64_to_element(u64::from(BETA)));
}

#[test]
fn inverses_and_serialization_are_canonical() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let a = compile.from_coefficients([1, 2, 3, 4, 5, 6]);
    assert_eq!(compile.mulf(&a, &compile.invert(&a)), compile.one());

    let runtime_a = runtime.from_compile(&a);
    assert_eq!(
        runtime.mulf(&runtime_a, &runtime.invert(&runtime_a)),
        runtime.one()
    );
    let words = runtime.to_words64(&runtime_a);
    assert_eq!(runtime.words64_to_element(&words).unwrap(), runtime_a);

    let mut invalid = runtime.to_bytes(&runtime.zero());
    invalid[..3].copy_from_slice(&Q.to_le_bytes()[..3]);
    assert!(runtime.bytes_to_element(&invalid).is_err());

    for coefficients in [
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [Q - 1, Q - 2, 17, 29, 31, 37],
    ] {
        let value = compile.from_coefficients(coefficients);
        assert_eq!(compile.mulf(&value, &compile.invert(&value)), compile.one());
    }
}

#[test]
fn base_subfield_is_distinct_from_the_extension() {
    let runtime = RuntimeFp24Ext6::new();
    let subfield = RuntimeFp24Subfield;
    let base = runtime.u64_to_element(1234);
    let extension = runtime.from_coefficients([1234, 1, 0, 0, 0, 0]);

    assert!(subfield.contains(&base));
    assert!(!subfield.contains(&extension));
    assert_eq!(
        subfield
            .bytes_to_element(&subfield.to_bytes(&base))
            .unwrap(),
        base
    );
}

#[test]
fn compact_fp24_encodings_are_exact_and_canonical() {
    let compile = CompileFp24Ext6::new();
    let runtime = RuntimeFp24Ext6::new();
    let subfield = RuntimeFp24Subfield;
    assert_eq!(compile.serialized_size_bytes(), 18);
    assert_eq!(runtime.serialized_size_bytes(), 18);
    assert_eq!(subfield.serialized_size_bytes(), 3);
    let coefficients = [1, 255, 256, 65_535, 65_536, Q - 1];
    let expected: Vec<_> = coefficients
        .iter()
        .flat_map(|c| c.to_le_bytes()[..3].to_vec())
        .collect();
    let value = runtime.from_coefficients(coefficients);
    assert_eq!(runtime.to_bytes(&value), expected);
    assert_eq!(
        compile.to_bytes(&compile.from_coefficients(coefficients)),
        expected
    );
    assert_eq!(runtime.bytes_to_element(&expected).unwrap(), value);
    assert_eq!(
        compile.bytes_to_element(&expected).unwrap(),
        compile.from_coefficients(coefficients)
    );
    let words = runtime.to_words64(&value);
    let word_bytes: Vec<_> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(&word_bytes[..18], expected);
    assert_eq!(&word_bytes[18..], &[0; 6]);
    assert_eq!(runtime.words64_to_element(&words).unwrap(), value);
    let mut bad_words = words;
    bad_words[2] |= 1 << 16;
    assert!(runtime.words64_to_element(&bad_words).is_err());
    for i in 0..6 {
        let mut bad = expected.clone();
        bad[3 * i..3 * i + 3].copy_from_slice(&Q.to_le_bytes()[..3]);
        assert!(runtime.bytes_to_element(&bad).is_err());
        assert!(compile.bytes_to_element(&bad).is_err());
    }
    for len in 0..=24 {
        if len != 18 {
            assert!(runtime.bytes_to_element(&vec![0; len]).is_err());
            assert!(compile.bytes_to_element(&vec![0; len]).is_err());
        }
        if len != 3 {
            assert!(subfield.bytes_to_element(&vec![0; len]).is_err());
        }
    }
    for coefficient in [0, 1, 255, 256, 65_535, 65_536, Q - 1] {
        let value = runtime.u64_to_element(u64::from(coefficient));
        let bytes = subfield.to_bytes(&value);
        assert_eq!(&bytes, &coefficient.to_le_bytes()[..3]);
        assert_eq!(subfield.bytes_to_element(&bytes).unwrap(), value);
    }
    assert!(subfield.bytes_to_element(&Q.to_le_bytes()[..3]).is_err());
}

fn bit_reverse_permute<T>(values: &mut [T]) {
    let mut reversed = 0;
    for i in 0..values.len() - 1 {
        if i < reversed {
            values.swap(i, reversed);
        }
        let mut bit = values.len();
        loop {
            bit >>= 1;
            reversed ^= bit;
            if reversed & bit != 0 {
                break;
            }
        }
    }
}

fn pow_base(mut base: u32, mut exponent: u32) -> u32 {
    let mut result = 1u32;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = (u64::from(result) * u64::from(base) % u64::from(Q)) as u32;
        }
        base = (u64::from(base) * u64::from(base) % u64::from(Q)) as u32;
        exponent >>= 1;
    }
    result
}

fn fft_fp24(values: &mut [u32]) {
    let n = values.len();
    bit_reverse_permute(values);
    let root = pow_base(283_817, (8192 / n) as u32);
    let mut roots = vec![1u32; n];
    for i in 1..n {
        roots[i] = (u64::from(roots[i - 1]) * u64::from(root) % u64::from(Q)) as u32;
    }
    let mut width = 2;
    while width <= values.len() {
        for block in values.chunks_exact_mut(width) {
            let (low, high) = block.split_at_mut(width / 2);
            let old_a = low[0];
            low[0] = if old_a + high[0] >= Q {
                old_a + high[0] - Q
            } else {
                old_a + high[0]
            };
            high[0] = if old_a >= high[0] {
                old_a - high[0]
            } else {
                old_a + Q - high[0]
            };
            for (j, (a, b)) in low.iter_mut().zip(high).enumerate().skip(1) {
                let twiddle = roots[j * n / width];
                let product = (u64::from(*b) * u64::from(twiddle) % u64::from(Q)) as u32;
                let previous = *a;
                *a = if previous + product >= Q {
                    previous + product - Q
                } else {
                    previous + product
                };
                *b = if previous >= product {
                    previous - product
                } else {
                    previous + Q - product
                };
            }
        }
        width *= 2;
    }
}

fn fft_fp24_6(
    field: &RuntimeFp24Ext6,
    values: &mut [circuits_experimental::mldsa::algebra::RuntimeElement],
) {
    assert_eq!(values.len(), 8192);
    let n = values.len();
    bit_reverse_permute(values);
    let root = field.u64_to_element(283_817);
    let mut roots = vec![field.one(); n];
    for i in 1..n {
        let previous = roots[i - 1];
        roots[i] = field.mulf(&previous, &root);
    }
    let mut width = 2;
    while width <= values.len() {
        for block in values.chunks_exact_mut(width) {
            let (low, high) = block.split_at_mut(width / 2);
            let old_a = low[0];
            let old_b = high[0];
            field.add(&mut low[0], &old_b);
            high[0] = old_a;
            field.sub(&mut high[0], &old_b);
            for (j, (a, b)) in low.iter_mut().zip(high).enumerate().skip(1) {
                let twiddle = roots[j * n / width];
                let mut product = *b;
                field.mul(&mut product, &twiddle);
                let previous = *a;
                field.add(a, &product);
                *b = previous;
                field.sub(b, &product);
            }
        }
        width *= 2;
    }
}

#[test]
#[ignore = "microbenchmark; run with --release --ignored --nocapture"]
fn mldsa_field_and_crt_benchmark() {
    const N: usize = 8192;
    let mut base: Vec<_> = (0..N)
        .map(|i| ((i as u64 * 1_103_515_245 + 12_345) % u64::from(Q)) as u32)
        .collect();
    let base_start = std::time::Instant::now();
    for _ in 0..100 {
        fft_fp24(std::hint::black_box(&mut base));
    }
    let fp24 = base_start.elapsed() / 100;

    let field = RuntimeFp24Ext6::new();
    let mut extension: Vec<_> = (0..N)
        .map(|i| {
            field.from_coefficients(std::array::from_fn(|j| {
                ((i as u64 * 1_103_515_245 + j as u64 * 97 + 12_345) % u64::from(Q)) as u32
            }))
        })
        .collect();
    let extension_start = std::time::Instant::now();
    for _ in 0..20 {
        fft_fp24_6(&field, std::hint::black_box(&mut extension));
    }
    let fp24_6 = extension_start.elapsed() / 20;

    let factory = circuits_experimental::mldsa::crt::CrtReedSolomonFactory;
    let rs = factory.make(950, 5699);
    let mut codeword = vec![field.zero(); 5699];
    for (i, value) in codeword.iter_mut().take(950).enumerate() {
        *value = field.from_coefficients(std::array::from_fn(|j| {
            ((i * 131 + j * 17 + 1) % Q as usize) as u32
        }));
    }
    let crt_start = std::time::Instant::now();
    for _ in 0..20 {
        rs.interpolate(std::hint::black_box(&mut codeword));
    }
    let crt = crt_start.elapsed() / 20;

    eprintln!(
        "ML-DSA algebra benchmark: FFT Fp24/8192={fp24:?}; FFT Fp24_6/8192={fp24_6:?}; CRT RS(950,5699)={crt:?}"
    );
    std::hint::black_box((base, extension, codeword));
}
