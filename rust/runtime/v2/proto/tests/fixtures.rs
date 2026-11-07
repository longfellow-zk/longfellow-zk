// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::algebra::{BareField, SerializableField},
    runtime::algebra::gf2_128::{Gf2_128, Gf2_128Field},
};

/// A permissive field decoder must not weaken the v2 wire-format contract.
pub(super) struct Aliased(pub Gf2_128Field);
impl BareField for Aliased {
    type E = Gf2_128;
}
impl SerializableField for Aliased {
    fn is_binary(&self) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        16
    }
    fn to_bytes_into(&self, x: &Gf2_128, dst: &mut [u8]) {
        self.0.to_bytes_into(x, dst)
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<Gf2_128, String> {
        if b == [0xff; 16] {
            Ok(Gf2_128::from(0u128))
        } else {
            self.0.bytes_to_element(b)
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.0.serialized_mone()
    }
}
