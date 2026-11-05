// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact byte-stream contracts, independent of field storage and proof codecs.
use std::collections::VecDeque;

use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::algebra::{fp_generic::FpGenericField, SubfieldV1, SupportsSampling, LIMBS_PER_U64},
};

struct Draws {
    expected: VecDeque<Vec<u8>>,
    requests: Vec<usize>,
}
impl Draws {
    fn new(draws: impl IntoIterator<Item = Vec<u8>>) -> Self {
        Self {
            expected: draws.into_iter().collect(),
            requests: Vec::new(),
        }
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        let bytes = self.expected.pop_front().expect("unexpected retry");
        assert_eq!(
            n,
            bytes.len(),
            "sampler must request the minimum byte count"
        );
        self.requests.push(n);
        bytes
    }
    fn exhausted(&self) {
        assert!(
            self.expected.is_empty(),
            "sampler failed to reject overflow"
        );
    }
}
type WidePrime = FpGenericField<4, { 4 * LIMBS_PER_U64 }, { 8 * LIMBS_PER_U64 + 1 }>;

#[test]
fn prime_sampling_masks_exact_bits_and_ignores_storage_padding() {
    // Odd prime moduli in 256-bit storage; includes partial bytes, exact byte
    // boundaries and a modulus with two entirely unused storage words.
    for (modulus, bits) in [
        ([3, 0, 0, 0], 2usize),
        ([257, 0, 0, 0], 9),
        ([1009, 0, 0, 0], 10),
        ([65537, 0, 0, 0], 17),
        ([8_380_417, 0, 0, 0], 23),
        ([0xffff_fffb, 0, 0, 0], 32),
        ([0xffff_ffff_ffff_ffc5, 0, 0, 0], 64),
        ([0xffff_ffff_ffff_ff61, u64::MAX, 0, 0], 128),
    ] {
        let f = WidePrime::new_generic(modulus);
        let byte_count = bits.div_ceil(8);
        let mut bound = modulus
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>();
        bound.truncate(byte_count);
        let maximum = (num_bigint::BigUint::from_bytes_le(&bound) - num_bigint::BigUint::from(1u8))
            .to_bytes_le();
        let mut padded = maximum.clone();
        padded.resize(byte_count, 0);
        if bits % 8 != 0 {
            *padded.last_mut().unwrap() |= u8::MAX << (bits % 8);
        }
        let mut draws = Draws::new([bound, padded]);
        let x = f.sample(|n| draws.bytes(n));
        draws.exhausted();
        assert_eq!(draws.requests, vec![byte_count, byte_count]);
        assert_eq!(
            num_bigint::BigUint::from_bytes_le(&f.to_bytes(&x)),
            num_bigint::BigUint::from_bytes_le(&maximum)
        );
    }
}
fn full_width_prime<F: SupportsSampling + SerializableField>(f: &F) {
    let p = (num_bigint::BigUint::from_bytes_le(&f.serialized_mone())
        + num_bigint::BigUint::from(1u8))
    .to_bytes_le();
    assert_eq!(p.len(), 32);
    let max =
        (num_bigint::BigUint::from_bytes_le(&p) - num_bigint::BigUint::from(1u8)).to_bytes_le();
    let mut draws = Draws::new([p, max.clone()]);
    let x = f.sample(|n| draws.bytes(n));
    draws.exhausted();
    assert_eq!(draws.requests, [32, 32]);
    assert_eq!(f.to_bytes(&x), max);
}
#[test]
fn p256_q256_and_v1_p256_sampling_keep_their_byte_contract() {
    use crate::runtime::algebra::{
        p256::{P256Field, P256SubfieldV1},
        q256::Q256Field,
    };
    let f = P256Field::new();
    full_width_prime(&f);
    full_width_prime(&Q256Field::new());
    let mut draws = Draws::new([vec![0xff; 32], vec![0; 32]]);
    assert_eq!(P256SubfieldV1::new(&f).sample(|n| draws.bytes(n)), f.zero());
    draws.exhausted();
    assert_eq!(draws.requests, [32, 32]);
}
#[test]
fn binary_field_and_subfields_use_all_and_only_the_required_bits() {
    use crate::runtime::algebra::{
        gf2_128::{Gf2_128, Gf2_128Field},
        subfield_v1::BinarySubfieldV1,
    };
    let mut draws = Draws::new([vec![0xff; 16]]);
    assert_eq!(
        Gf2_128Field::new().sample(|n| draws.bytes(n)),
        Gf2_128::from(u128::MAX)
    );
    draws.exhausted();
    for count in [8, 16] {
        let sf = BinarySubfieldV1::new(&crate::core::algebra::proto::GF2_16_BASIS_V1[..count]);
        let mut subfield_draws = Draws::new([vec![0xff; count / 8]]);
        assert_eq!(
            sf.sample(|n| subfield_draws.bytes(n)),
            sf.embed((1u64 << count) - 1)
        );
        subfield_draws.exhausted();
    }
}
#[test]
fn sextic_sampling_reads_three_bytes_and_masks_23_bits_per_coordinate() {
    use crate::runtime::algebra::fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24SubfieldV1, Q};
    let f = RuntimeFp24Ext6;
    let mut draws =
        Draws::new([Q, 0x80_0001, 2, 3, 4, 5, Q - 1].map(|x| x.to_le_bytes()[..3].to_vec()));
    let sampled = f.sample(|n| draws.bytes(n));
    assert_eq!(sampled.coefficients(), &[1, 2, 3, 4, 5, Q - 1]);
    draws.exhausted();
    assert_eq!(draws.requests, vec![3; 7]);
    let inputs = [Q, Q + 1, (Q - 1) | 0x80_0000].map(|x| x.to_le_bytes()[..3].to_vec());
    let mut legacy = Draws::new(inputs);
    let sampled_base = RuntimeFp24SubfieldV1.sample(|n| legacy.bytes(n));
    assert_eq!(sampled_base.coefficients(), &[Q - 1, 0, 0, 0, 0, 0]);
    assert!(RuntimeFp24SubfieldV1.contains(&sampled_base));
    legacy.exhausted();
    assert_eq!(legacy.requests, [3, 3, 3]);
    let mut no_rejections = Draws::new((0..6).map(|i| vec![i, 0, 0]));
    f.sample(|n| no_rejections.bytes(n));
    no_rejections.exhausted();
    assert_eq!(no_rejections.requests.iter().sum::<usize>(), 18);
}
