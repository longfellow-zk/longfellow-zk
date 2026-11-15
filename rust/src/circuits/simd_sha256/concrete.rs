// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::INPUT_BITS;
use crate::{
    circuits::{sha256, sha256::Given},
    core::algebra::AlgebraicField,
    runtime::algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
};
pub fn pack_instances(instances: &[Given<u32>]) -> Vec<E> {
    assert_eq!(instances.len(), 128);
    let mut out = vec![F::new().zero(); INPUT_BITS];
    for (lane, given) in instances.iter().enumerate() {
        let derived = sha256::derived(given);
        let mut word = 0;
        let mut push = |&value: &u32| {
            for bit in 0..32 {
                out[word * 32 + bit] = E::from(
                    out[word * 32 + bit].to_u128() | (u128::from(value >> bit & 1) << lane),
                );
            }
            word += 1;
        };
        given.for_each(&mut push);
        derived.for_each(&mut push);
        assert_eq!(word * 32, INPUT_BITS);
    }
    out
}
