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

use crate::{
    core::algebra::{
        AlgebraicField, Nat, SerializableField, SupportsNatConversions, SupportsU64Conversions,
    },
    runtime::algebra::{
        fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Subfield, Q},
        RuntimeField, RuntimeNat, SubfieldV1, SupportsSampling,
    },
};

#[test]
fn runtime_field_laws_and_natural_reduction() {
    let f = RuntimeFp24Ext6::new();
    for i in 1..65 {
        let a = f.from_coefficients(std::array::from_fn(|j| (i * 97 + j as u32 * 131) % Q));
        let b = f.from_coefficients(std::array::from_fn(|j| (i * 31 + j as u32 * 257) % Q));
        let c = f.from_coefficients(std::array::from_fn(|j| (Q - i + j as u32) % Q));
        assert_eq!(
            f.mulf(&a, &f.addf(&b, &c)),
            f.addf(&f.mulf(&a, &b), &f.mulf(&a, &c))
        );
        assert_eq!(f.mulf(&a, &f.invert(&a)), f.one());
        assert_eq!(f.bytes_to_element(&f.to_bytes(&a)).unwrap(), a);
        let mut accum = f.zero_accum();
        f.mac(&mut accum, &a, &b);
        f.mac(&mut accum, &a, &c);
        assert_eq!(f.accum_reduce(&accum), f.mulf(&a, &f.addf(&b, &c)));
    }
    for limbs in [
        [0, 0, 0],
        [u64::from(Q), 0, 0],
        [0, 1, 0],
        [0, 0, 1],
        [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x100],
        [u64::MAX, u64::MAX, u64::MAX],
    ] {
        let n = <RuntimeNat<3> as Nat<3>>::from_limbs(&limbs);
        // Independent bitwise reduction catches limb/byte-order mistakes.
        let mut expected = 0u64;
        for bit in (0..192).rev() {
            expected = (expected * 2 + ((limbs[bit / 64] >> (bit % 64)) & 1)) % u64::from(Q);
        }
        assert_eq!(f.reduce_nat(&n), f.u64_to_element(expected));
    }
    assert_eq!(
        f.reduce_nat(&f.to_nat(&f.u64_to_element(12345))),
        f.u64_to_element(12345)
    );
}

#[test]
fn sampling_rejects_noncanonical_candidates_in_extension_and_subfield() {
    let f = RuntimeFp24Ext6::new();
    let mut candidates = [Q, Q + 1, 0, 1, 2, 3, 4, Q - 1].into_iter();
    let sampled = f.sample(|n| {
        assert_eq!(n, 3);
        candidates.next().unwrap().to_le_bytes()[..3].to_vec()
    });
    assert_eq!(sampled, f.from_coefficients([0, 1, 2, 3, 4, Q - 1]));
    let mut base_candidates = [Q, 42].into_iter();
    let base_sample = RuntimeFp24Subfield.sample(|n| {
        assert_eq!(n, 3);
        base_candidates.next().unwrap().to_le_bytes()[..3].to_vec()
    });
    assert_eq!(base_sample, f.u64_to_element(42));
    assert!(RuntimeFp24Subfield.contains(&base_sample));
}
