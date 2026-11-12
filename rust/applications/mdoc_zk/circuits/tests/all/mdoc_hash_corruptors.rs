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

#![allow(dead_code)]

use crate::{
    compile::algebra::CompileNat, core::algebra::Nat, mdoc::circuits::hash::concrete::ConcreteGiven,
};

pub(super) struct MdocHashCorruptor {
    pub name: String,
    pub expected_path: String,
    pub corrupt: Box<dyn Fn(&mut ConcreteGiven<CompileNat<4>>)>,
}

pub(super) fn all_mdoc_hash_corruptors() -> Vec<MdocHashCorruptor> {
    vec![
        MdocHashCorruptor {
            name: "wrong_global_namespace".into(),
            expected_path: "assert_valid_presentation/assert_mso_namespace/value_bytes/value_bytes.0/text_byte".into(),
            corrupt: Box::new(|g| { g.hash_input.expected_namespace[0] ^= 1; }),
        },
        MdocHashCorruptor {
            name: "empty_global_namespace".into(),
            expected_path: "assert_valid_presentation/assert_mso_namespace/text_length".into(),
            corrupt: Box::new(|g| { g.hash_input.expected_namespace.clear(); }),
        },
        MdocHashCorruptor {
            name: "namespace_offset_before_signed_map".into(),
            expected_path: "assert_valid_presentation/assert_mso_namespace/shift_preimage_bounds/ge_mso".into(),
            corrupt: Box::new(|g| { g.namespace_offset_in_preimage = 25; }),
        },
        MdocHashCorruptor {
            name: "namespace_in_cose_framing".into(),
            expected_path: "assert_valid_presentation/assert_mso_namespace/shift_preimage_bounds/ge_mso".into(),
            corrupt: Box::new(|g| { g.hash_input.expected_namespace = b"t".to_vec(); g.namespace_offset_in_preimage = 6; }),
        },
        MdocHashCorruptor {
            name: "namespace_aliases_value_digests_header".into(),
            expected_path: "assert_valid_presentation/assert_mso_namespace/after_value_digests".into(),
            corrupt: Box::new(|g| { g.hash_input.expected_namespace = b"l".to_vec(); g.namespace_offset_in_preimage = g.value_digests_offset_in_preimage + 2; }),
        },
        MdocHashCorruptor {
            name: "namespace_after_attribute_digest".into(),
            expected_path: "assert_valid_presentation/assert_attributes/assert_attributes.0/attribute_item/namespace_before_digest/lt".into(),
            corrupt: Box::new(|g| { g.namespace_offset_in_preimage = g.attribute_given[0].mso_digest_offset_in_preimage as u16 + 34; }),
        },
        MdocHashCorruptor {
            name: "corrupt_issuer_sig_e".into(),
            expected_path:
                "assert_valid_presentation/assert_message_hash/hash_eq/hash_eq.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                g.hash_input.issuer_sig_e = CompileNat::<4>::from_u64(0xdeadbeef);
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_preimage_byte".into(),
            expected_path:
                "assert_valid_presentation/assert_message_hash/assert_intermediate_hashes/assert_intermediate_hashes.0/sha256/schedule/schedule.1/assert_wrapping_sum_gf2"
                    .into(),
            corrupt: Box::new(|g| {
                g.preimage.value[10] ^= 1;
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_doc_type_offset".into(),
            expected_path:
                "assert_valid_presentation/assert_mso_doc_type/cbor_header/cbor_header.0/header_byte"
                    .into(),
            corrupt: Box::new(|g| {
                g.doc_type_offset_in_preimage += 1;
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_valid_from_offset".into(),
            expected_path:
                "assert_valid_presentation/assert_mso_validity/valid_from/assert_bytes_at/assert_bytes_at.0/bytes_at/bytes_at.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                g.valid_from_offset_in_preimage += 1;
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_valid_until_offset".into(),
            expected_path:
                "assert_valid_presentation/assert_mso_validity/valid_until/assert_bytes_at/assert_bytes_at.0/bytes_at/bytes_at.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                g.valid_until_offset_in_preimage += 1;
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_dev_key_info_offset".into(),
            expected_path:
                "assert_valid_presentation/assert_mso_device_key/assert_bytes_at/assert_bytes_at.0/bytes_at/bytes_at.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                g.dev_key_info_offset_in_preimage += 1;
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_value_digests_offset".into(),
            expected_path:
                "assert_valid_presentation/assert_mso_value_digests/assert_bytes_at/assert_bytes_at.0/bytes_at/bytes_at.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                g.value_digests_offset_in_preimage += 1;
            }),
        },




        MdocHashCorruptor {
            name: "corrupt_attribute_permutation_duplicate".into(),
            expected_path:
                "assert_valid_presentation/assert_attributes/assert_attributes.0/attribute_item/assert_attribute/assert_permutation/assert_permutation.0/perm_neq"
                    .into(),
            corrupt: Box::new(|g| {
                if let Some(attr) = g.attribute_given.get_mut(0) {
                    attr.field_locator.permutation = 1 | (1 << 2) | (2 << 4) | (3 << 6);
                }
            }),
        },
        MdocHashCorruptor {
            name: "corrupt_attribute_permutation_swap".into(),
            expected_path:
                "assert_valid_presentation/assert_attributes/assert_attributes.0/attribute_item/assert_attribute/assert_item_slot_key_only/assert_bytes_at/assert_bytes_at.0/bytes_at/bytes_at.0/chunk_eq"
                    .into(),
            corrupt: Box::new(|g| {
                if let Some(attr) = g.attribute_given.get_mut(0) {
                    attr.field_locator.permutation = 1 | (2 << 4) | (3 << 6);
                }
            }),
        },
    ]
}
