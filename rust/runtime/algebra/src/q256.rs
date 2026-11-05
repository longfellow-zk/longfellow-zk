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

use crate::runtime::algebra::fp_generic::{FpGenericElement, FpGenericField};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Q256Tag;

pub type Q256Element = FpGenericElement<{ 4 * crate::runtime::algebra::LIMBS_PER_U64 }, Q256Tag>;
pub type Q256Field = FpGenericField<
    4,
    { 4 * crate::runtime::algebra::LIMBS_PER_U64 },
    { 9 * crate::runtime::algebra::LIMBS_PER_U64 },
    Q256Tag,
>;

const Q256_MODULUS: [u64; 4] = [
    0xf3b9cac2fc632551,
    0xbce6faada7179e84,
    0xffffffffffffffff,
    0xffffffff00000000,
];

impl Default for Q256Field {
    fn default() -> Self {
        Self::new()
    }
}

impl Q256Field {
    #[must_use]
    pub fn new() -> Self {
        Self::new_generic(Q256_MODULUS)
    }
}

impl crate::runtime::algebra::packing::PackingField for Q256Field {
    type Packing = crate::runtime::algebra::packing::IdentityExtension<Self>;
    fn packing_extension(&self) -> Self::Packing {
        crate::runtime::algebra::packing::IdentityExtension::new(self.clone())
    }
    fn packing_id(&self) -> Vec<u8> {
        let mut id = b"prime/canonical-integer/v1/".to_vec();
        id.extend_from_slice(&crate::core::algebra::SerializableField::serialized_mone(
            self,
        ));
        id
    }
}
