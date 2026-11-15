// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::fp24::Q,
    mldsa::{proto::BinaryKeccak, runtime::reference::ConcreteInstance},
};
fn bits(destination: &mut Vec<bool>, value: u64, width: usize) {
    destination.extend((0..width).map(|i| value >> i & 1 != 0));
}
fn groups<P: MlDsaParams>(instance: &ConcreteInstance<P>) -> Vec<bool> {
    let mut out = Vec::new();
    for row in &instance.signature.z_bits {
        for &value in row {
            bits(&mut out, value, P::Z_BITS);
        }
    }
    {
        for row in &instance.signature.h {
            for &value in row {
                bits(&mut out, u64::from(value), 1);
            }
        }
    }
    {
        for row in &instance.witness.raw_high_bits {
            for &value in row {
                bits(&mut out, value, P::R1_BITS);
            }
        }
    }
    for row in &instance.witness.hint_auxiliary_bits {
        for &value in row {
            bits(&mut out, value, P::r0_bits() + 1);
        }
    }
    {
        for row in &instance.witness.hinted_high_bits {
            for &value in row {
                bits(&mut out, value, P::R1_BITS);
            }
        }
    }
    out.extend(instance.witness.c.iter().map(|&x| x == 1));
    out.extend(instance.witness.c.iter().map(|&x| x == Q - 1));
    out
}

pub(crate) fn binary_inputs<P: MlDsaParams>(
    instance: &ConcreteInstance<P>,
    keccak: BinaryKeccak,
) -> Vec<bool> {
    let mut binary = groups(instance);
    let push_bytes = |destination: &mut Vec<bool>, bytes: &[u8]| {
        destination.extend(
            bytes
                .iter()
                .flat_map(|&byte| (0..8).map(move |i| byte >> i & 1 != 0)),
        );
    };
    push_bytes(&mut binary, &instance.signature.c_tilde);
    let sample = &instance.witness.sample;
    binary.extend(sample.binary_bits_with_keccak(keccak));
    binary.extend(instance.witness.challenge_hash.bits_with_keccak(keccak));
    push_bytes(&mut binary, &instance.mu);
    binary
}
