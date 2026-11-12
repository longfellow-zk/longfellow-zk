// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only check that application gates cannot inspect adapter randomness.
use crate::core::proto::{v2::RawCircuit, SerializableField};

/// Check the input-facing layer, including zero-coefficient assertion records.
/// All later application layers read only preceding application wires. The
/// runtime builds the adapter as a separate circuit, with its own coefficients
/// and intermediate wires, over the same input array.
pub(crate) fn validate<F: SerializableField>(circuit: &RawCircuit<F>) -> Result<(), String> {
    let end = circuit
        .ninput
        .checked_sub(super::AUXILIARY_BITS)
        .filter(|&end| end >= circuit.npublic_input)
        .ok_or("hash circuit is missing the private adapter suffix")?;
    let input = circuit.layers.last().ok_or("empty hash circuit")?;
    if input.nw != circuit.ninput {
        return Err("hash circuit input width mismatch".into());
    }
    let check = |wire: u32| {
        if (wire as usize) < end {
            Ok(())
        } else {
            Err("hash circuit reads adapter mask or OTP inputs".to_owned())
        }
    };
    input.quadratic.try_for_each(|term| {
        check(term.l)?;
        check(term.r)
    })?;
    input.linear.try_for_each(|term| check(term.l))
}

#[cfg(test)]
#[path = "../../tests/p256_adapter_hash_inputs.rs"]
mod tests;
