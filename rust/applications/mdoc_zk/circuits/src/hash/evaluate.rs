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

use super::{
    circuit::{
        AttrDerived as WireAttrDerived, AttrGiven as WireAttrGiven,
        AttrPreimageBytes as WireAttrPreimageBytes, Derived as WireDerived, Given as WireGiven,
        MsoPreimageBytes as WireMsoPreimageBytes,
    },
    concrete::{ConcreteDerived, ConcreteGiven},
    constants::K_HASH_INDEX_BITS,
};
use crate::{
    circuits::bitvec::BitvecLogic,
    core::algebra::Nat,
    mdoc::circuits::mso_attribute::{
        circuit::{
            AttrSlice as MsoSlice, DisclosedAttribute as WireDisclosedAttribute,
            FieldLocator as WireFieldLocator,
        },
        constants::K_ATTR_INDEX_BITS,
    },
};

pub fn evaluate_given<L: crate::compile::logic::LogicIO>(
    logic: &L,
    bv: &BitvecLogic<L>,
    given: &ConcreteGiven<crate::compile::algebra::CompileNat<4>>,
) -> WireGiven<L> {
    let boolean = crate::circuits::boolean::Boolean::new(logic);

    let get_byte = |bytes: &[u8], idx: usize| {
        if idx < bytes.len() {
            bytes[idx]
        } else {
            0
        }
    };

    let disclosed_attributes: Vec<WireDisclosedAttribute<L>> = given
        .hash_input
        .attrs
        .iter()
        .map(|a| WireDisclosedAttribute {
            expected_name: MsoSlice {
                data: std::array::from_fn(|i| {
                    let bit_val = get_byte(&a.expected_name, i);
                    bv.of_u64::<8>(u64::from(bit_val))
                }),
                len: bv.of_u64::<K_ATTR_INDEX_BITS>(a.expected_name.len() as u64),
            },
            expected_cbor_value: MsoSlice {
                data: std::array::from_fn(|i| {
                    let bit_val = get_byte(&a.expected_cbor_value, i);
                    bv.of_u64::<8>(u64::from(bit_val))
                }),
                len: bv.of_u64::<K_ATTR_INDEX_BITS>(a.expected_cbor_value.len() as u64),
            },
        })
        .collect();

    let now = std::array::from_fn(|i| {
        let bit_val = get_byte(&given.hash_input.now, i);
        bv.of_u64::<8>(u64::from(bit_val))
    });

    let preimage = WireMsoPreimageBytes {
        value: std::array::from_fn(|i| {
            let bit_val = get_byte(&given.preimage.value, i);
            bv.of_u64::<8>(u64::from(bit_val))
        }),
        len: bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.preimage.len)),
    };

    let nblocks = bv.of_u64::<8>(u64::from(given.nblocks));

    let mut issuer_sig_e_bytes = given.hash_input.issuer_sig_e.to_bytes_le();
    issuer_sig_e_bytes.resize(32, 0);
    let issuer_sig_e = bv.from_fn::<256, _>(|idx| {
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        let byte = issuer_sig_e_bytes[byte_idx];
        let bit_val = (byte.checked_shr(bit_idx as u32).unwrap_or(0) & 1) == 1;
        boolean.konst(bit_val)
    });

    let mut dpk0_bytes = given.hash_input.device_pk.0.to_bytes_le();
    dpk0_bytes.resize(32, 0);
    let mut dpk1_bytes = given.hash_input.device_pk.1.to_bytes_le();
    dpk1_bytes.resize(32, 0);

    let device_pk = (
        bv.from_fn::<256, _>(|idx| {
            let byte_idx = idx / 8;
            let bit_idx = idx % 8;
            let byte = dpk0_bytes[byte_idx];
            let bit_val = (byte.checked_shr(bit_idx as u32).unwrap_or(0) & 1) == 1;
            boolean.konst(bit_val)
        }),
        bv.from_fn::<256, _>(|idx| {
            let byte_idx = idx / 8;
            let bit_idx = idx % 8;
            let byte = dpk1_bytes[byte_idx];
            let bit_val = (byte.checked_shr(bit_idx as u32).unwrap_or(0) & 1) == 1;
            boolean.konst(bit_val)
        }),
    );

    let doc_type_offset_in_preimage =
        bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.doc_type_offset_in_preimage));
    let valid_from_offset_in_preimage =
        bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.valid_from_offset_in_preimage));
    let valid_until_offset_in_preimage =
        bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.valid_until_offset_in_preimage));
    let dev_key_info_offset_in_preimage =
        bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.dev_key_info_offset_in_preimage));
    let value_digests_offset_in_preimage =
        bv.of_u64::<K_HASH_INDEX_BITS>(u64::from(given.value_digests_offset_in_preimage));

    let mut attribute_given = Vec::with_capacity(given.attribute_given.len());
    for a in &given.attribute_given {
        attribute_given.push(WireAttrGiven {
            preimage: WireAttrPreimageBytes {
                data: std::array::from_fn(|i| {
                    let bit_val = get_byte(&a.padded_preimage, i);
                    bv.of_u64::<8>(u64::from(bit_val))
                }),
                len: bv.of_u64::<K_ATTR_INDEX_BITS>(a.unpadded_preimage_len as u64),
            },
            mso_digest_offset_in_preimage: bv
                .of_u64::<K_HASH_INDEX_BITS>(a.mso_digest_offset_in_preimage as u64),
            field_locator: WireFieldLocator {
                slot_position: std::array::from_fn(|j| {
                    bv.of_u64::<K_ATTR_INDEX_BITS>(a.field_locator.slot_position[j] as u64)
                }),
                length: std::array::from_fn(|j| {
                    bv.of_u64::<K_ATTR_INDEX_BITS>(a.field_locator.length[j] as u64)
                }),
                permutation: std::array::from_fn(|j| {
                    let slot = (a.field_locator.permutation >> (2 * j)) & 3;
                    bv.of_u64::<2>(slot as u64)
                }),
            },
        });
    }

    let suppress_doc_type_check = boolean.konst(given.hash_input.suppress_doc_type_check);
    let expected_doc_type = MsoSlice {
        data: std::array::from_fn(|i| {
            let bit_val = get_byte(&given.hash_input.expected_doc_type, i);
            bv.of_u64::<8>(u64::from(bit_val))
        }),
        len: bv.of_u64::<K_ATTR_INDEX_BITS>(given.hash_input.expected_doc_type.len() as u64),
    };

    WireGiven {
        disclosed_attributes,
        now,
        suppress_doc_type_check,
        expected_doc_type,
        preimage,
        nblocks,
        issuer_sig_e,
        device_pk,
        doc_type_offset_in_preimage,
        valid_from_offset_in_preimage,
        valid_until_offset_in_preimage,
        dev_key_info_offset_in_preimage,
        value_digests_offset_in_preimage,
        attribute_given,
    }
}

pub fn evaluate_derived<L: crate::compile::logic::LogicIO>(
    _logic: &L,
    bv: &BitvecLogic<L>,
    derived: &ConcreteDerived,
) -> WireDerived<L> {
    let mut attribute_derived = Vec::with_capacity(derived.attribute_derived.len());
    for a in &derived.attribute_derived {
        let sha_derived =
            crate::circuits::sha256msg::evaluate::evaluate_derived(&a.sha_derived, bv);
        attribute_derived.push(WireAttrDerived { sha_derived });
    }

    let sha_derived =
        crate::circuits::sha256msg::evaluate::evaluate_derived(&derived.sha_derived, bv);

    WireDerived {
        attribute_derived,
        sha_derived,
    }
}
