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
    compile::compiler::CompilerLogic,
    mdoc::{
        circuits::{
            hash::{
                circuit::{
                    AttrDerived, AttrGiven, AttrPreimageBytes, Derived as HashDerived,
                    MsoPreimageBytes,
                },
                constants::{
                    K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS, K_MSO_PREIMAGE_LEN, K_TIMESTAMP_LEN,
                },
            },
            mso_attribute::{
                constants::{K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN},
                AttrSlice, DisclosedAttribute, FieldLocator,
            },
            MdocHashCompileField,
        },
        compile::allocator::WireAllocator,
    },
};

pub fn allocate_disclosed_attribute<'b, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
) -> DisclosedAttribute<CompilerLogic<'b, FC>> {
    let name = allocator.allocate_bitvec_array::<8, 32>();
    let name_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();

    let value = allocator.allocate_bitvec_array::<8, 64>();
    let value_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();

    DisclosedAttribute {
        expected_name: AttrSlice {
            data: name,
            len: name_len,
        },
        expected_cbor_value: AttrSlice {
            data: value,
            len: value_len,
        },
    }
}

pub fn sha256_block_wires<'a, 'b, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'a, 'b, FC>,
) -> crate::circuits::sha256::Derived<CompilerLogic<'b, FC>> {
    crate::circuits::sha256::Derived {
        outw: std::array::from_fn(|_| allocator.allocate_bitvec::<32>()),
        oute: std::array::from_fn(|_| allocator.allocate_bitvec::<32>()),
        outa: std::array::from_fn(|_| allocator.allocate_bitvec::<32>()),
        h1: std::array::from_fn(|_| allocator.allocate_bitvec::<32>()),
    }
}

pub fn allocate_sha_derived<'b, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    max_blocks: usize,
) -> Vec<crate::circuits::sha256::Derived<CompilerLogic<'b, FC>>> {
    (0..max_blocks)
        .map(|_| sha256_block_wires(allocator))
        .collect()
}

pub fn allocate_attr_wires<'a, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'a, FC>,
) -> (
    AttrGiven<CompilerLogic<'a, FC>>,
    AttrDerived<CompilerLogic<'a, FC>>,
) {
    let preimage_value = allocator.allocate_bitvec_array::<8, K_ATTR_PREIMAGE_LEN>();
    let preimage_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();
    let preimage = AttrPreimageBytes {
        data: preimage_value,
        len: preimage_len,
    };
    let mso_digest_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|_| {
            allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>()
        }),
        length: std::array::from_fn(|_| allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>()),
        permutation: std::array::from_fn(|_| allocator.allocate_bitvec::<2>()),
    };
    let sha_derived = allocate_sha_derived(allocator, 2);
    let given = AttrGiven {
        preimage,
        mso_digest_offset_in_preimage,
        field_locator,
    };
    let derived = AttrDerived { sha_derived };
    (given, derived)
}

pub fn allocate_hash_core<'b, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    num_attrs: usize,
) -> (
    crate::mdoc::circuits::hash::circuit::Given<CompilerLogic<'b, FC>>,
    HashDerived<CompilerLogic<'b, FC>>,
    usize,
) {
    let now = allocator.allocate_bitvec_array::<8, K_TIMESTAMP_LEN>();

    let disclosed_attributes = (0..num_attrs)
        .map(|_| allocate_disclosed_attribute(allocator))
        .collect();

    allocate_body(allocator, num_attrs, now, disclosed_attributes)
}

fn allocate_body<'b, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    num_attrs: usize,
    now: [crate::circuits::bitvec::V8<CompilerLogic<'b, FC>>; K_TIMESTAMP_LEN],
    disclosed_attributes: Vec<DisclosedAttribute<CompilerLogic<'b, FC>>>,
) -> (
    crate::mdoc::circuits::hash::circuit::Given<CompilerLogic<'b, FC>>,
    HashDerived<CompilerLogic<'b, FC>>,
    usize,
) {
    let boolean_io = crate::circuits::boolean::BooleanIO::new(allocator.iologic);
    let suppress_doc_type_check = boolean_io.next(&mut allocator.pos);
    let expected_doc_type_bytes = allocator.allocate_bitvec_array::<8, 32>();
    let expected_doc_type_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();
    let expected_doc_type = crate::mdoc::circuits::mso_attribute::circuit::AttrSlice {
        data: expected_doc_type_bytes,
        len: expected_doc_type_len,
    };

    let pub_inputs_count = allocator.pos;

    let issuer_sig_e = allocator.allocate_bitvec::<256>();
    let preimage_value = allocator.allocate_bitvec_array::<8, K_MSO_PREIMAGE_LEN>();
    let len = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let preimage = MsoPreimageBytes {
        value: preimage_value,
        len,
    };
    let nblocks = allocator.allocate_bitvec::<8>();

    let device_pk_x = allocator.allocate_bitvec::<256>();
    let device_pk_y = allocator.allocate_bitvec::<256>();
    let device_pk = (device_pk_x, device_pk_y);

    let doc_type_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let valid_from_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let valid_until_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let dev_key_info_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let value_digests_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();

    let mut attribute_given = Vec::with_capacity(num_attrs);
    let mut attribute_derived = Vec::with_capacity(num_attrs);

    for _ in 0..num_attrs {
        let (given, derived) = allocate_attr_wires(allocator);
        attribute_given.push(given);
        attribute_derived.push(derived);
    }

    let sha_derived = allocate_sha_derived(allocator, K_MAX_SHA_BLOCKS);

    let presentation = crate::mdoc::circuits::hash::circuit::Given {
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
    };

    let derived = HashDerived {
        attribute_derived,
        sha_derived,
    };

    (presentation, derived, pub_inputs_count)
}
