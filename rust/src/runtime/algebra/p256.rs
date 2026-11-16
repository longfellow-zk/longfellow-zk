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
    core::algebra::{FieldID, RegisteredField, Sealed, SerializableField},
    runtime::algebra::{
        fp2::{Fp2Element, Fp2Field},
        fp_generic::{FpGenericElement, FpGenericField},
        limb::{words64_to_limbs, Limb, LIMBS_PER_U64},
        packing::{IdentityExtension, PackingField},
        RuntimeSerializableField, SupportsFFT, SupportsQuadraticExtension,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct P256Tag;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct P256Strategy;

pub type P256Element = FpGenericElement<{ 4 * LIMBS_PER_U64 }, P256Tag>;
pub type P256Field =
    FpGenericField<4, { 4 * LIMBS_PER_U64 }, { 9 * LIMBS_PER_U64 }, P256Tag, P256Strategy>;

const P256_MODULUS: [u64; 4] = [
    0xffffffffffffffff,
    0x00000000ffffffff,
    0x0000000000000000,
    0xffffffff00000001,
];

/// Whether `modulo` is the P-256 prime, the only modulus whose reduction
/// `P256Strategy` implements.
fn is_p256_modulus(modulo: &[Limb; 4 * LIMBS_PER_U64]) -> bool {
    *modulo == words64_to_limbs::<4, { 4 * LIMBS_PER_U64 }>(&P256_MODULUS)
}

#[cfg(all(target_pointer_width = "64", not(feature = "force-32bit-limbs")))]
mod p256_64;

#[cfg(any(target_pointer_width = "32", feature = "force-32bit-limbs"))]
mod p256_32;

impl Default for P256Field {
    fn default() -> Self {
        Self::new()
    }
}

impl P256Field {
    #[must_use]
    pub fn new() -> Self {
        Self::new_generic(P256_MODULUS)
    }
}

// The P-256 modulus is 3 modulo 4, so -1 is a quadratic nonresidue and
// `x^2 + 1` defines a genuine quadratic extension.
impl SupportsQuadraticExtension for P256Field {}

const P256_ROOT_OF_UNITY_RE: [u64; 4] = [
    0x985a65324b242562,
    0x9fc9563b382a4a4c,
    0x5cfc85c67990e337,
    0xf90d338ebd84f566,
];
const P256_ROOT_OF_UNITY_IM: [u64; 4] = [
    0xdbf4174f60a43eac,
    0x84738a6474d232c6,
    0xa04fc2e20106e340,
    0xb9e81e42bc97cc4d,
];

impl SupportsFFT for Fp2Field<'_, P256Field> {
    fn omega(&self) -> Self::E {
        Fp2Element {
            re: self
                .base_field()
                .words64_to_element(&P256_ROOT_OF_UNITY_RE)
                .unwrap(),
            im: self
                .base_field()
                .words64_to_element(&P256_ROOT_OF_UNITY_IM)
                .unwrap(),
        }
    }

    fn omega_order(&self) -> u64 {
        1u64 << 31
    }
}

impl Sealed for P256Field {}
/// FieldID::P256 names exactly this field, serialized in 32 bytes.
impl RegisteredField for P256Field {
    const ID: FieldID = FieldID::P256;
    const BYTES: usize = 32;
}

impl PackingField for P256Field {
    type Packing = IdentityExtension<Self>;
    fn packing_extension(&self) -> Self::Packing {
        IdentityExtension::new(self.clone())
    }
    fn packing_id(&self) -> Vec<u8> {
        let mut id = b"prime/canonical-integer/v1/".to_vec();
        id.extend_from_slice(&SerializableField::serialized_mone(self));
        id
    }
}
