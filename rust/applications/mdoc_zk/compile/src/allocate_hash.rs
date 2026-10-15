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

use circuits_bit_plucker::BitPlucker;
use compile_compiler::CompilerLogic;
use mdoc_zk_circuits::{
    config::{K_HASH_V256_BIT_PLUCKER, K_HASH_V8_BIT_PLUCKER, K_SHA_BIT_PLUCKER},
    hash::{
        circuit::{
            AttrDerived, AttrGiven, AttrPreimageBytes, Derived as HashDerived, Given as HashGiven,
            MsoPreimageBytes, PnymDerived, PnymGiven,
        },
        constants::{K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS, K_MSO_PREIMAGE_LEN, K_TIMESTAMP_LEN},
    },
    mso_attribute::{
        constants::{
            K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN, K_MAX_ATTR_SHA_BLOCKS, K_OP_BITS,
            K_PNYM_CONTEXT_BITS, K_PNYM_CONTEXT_MAX, K_PNYM_PREIMAGE_LEN, K_PNYM_SHA_BLOCKS,
            K_PNYM_VALUE_LEN,
        },
        AttrSlice, ContextSlice, DisclosedAttribute, DisclosedPnym, FieldLocator,
    },
    MdocHashCompileField,
};

use crate::allocator::WireAllocator;

pub fn allocate_disclosed_attribute<'b, FC: MdocHashCompileField, const PLUCKER_WIDTH: usize>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    plucker: &BitPlucker<'_, CompilerLogic<'b, FC>, PLUCKER_WIDTH>,
) -> DisclosedAttribute<CompilerLogic<'b, FC>> {
    let (name, _) = allocator.allocate_plucked_v8_array::<32, PLUCKER_WIDTH>(plucker);
    let name_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();

    let (value, _) = allocator.allocate_plucked_v8_array::<64, PLUCKER_WIDTH>(plucker);
    let value_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();
    let op = allocator.allocate_bitvec::<{ K_OP_BITS }>();

    DisclosedAttribute {
        expected_name: AttrSlice {
            data: name,
            len: name_len,
        },
        expected_cbor_value: AttrSlice {
            data: value,
            len: value_len,
        },
        op,
    }
}

pub fn allocate_disclosed_pnym<'b, FC: MdocHashCompileField, const PLUCKER_WIDTH: usize>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    plucker: &BitPlucker<'_, CompilerLogic<'b, FC>, PLUCKER_WIDTH>,
) -> DisclosedPnym<CompilerLogic<'b, FC>> {
    let (name, _) = allocator.allocate_plucked_v8_array::<32, PLUCKER_WIDTH>(plucker);
    let name_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();

    let (value, _) =
        allocator.allocate_plucked_v8_array::<K_PNYM_VALUE_LEN, PLUCKER_WIDTH>(plucker);
    let value_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();

    let (context, _) =
        allocator.allocate_plucked_v8_array::<K_PNYM_CONTEXT_MAX, PLUCKER_WIDTH>(plucker);
    let context_len = allocator.allocate_bitvec::<{ K_PNYM_CONTEXT_BITS }>();

    DisclosedPnym {
        expected_name: AttrSlice {
            data: name,
            len: name_len,
        },
        expected_cbor_value: AttrSlice {
            data: value,
            len: value_len,
        },
        context: ContextSlice {
            data: context,
            len: context_len,
        },
    }
}

pub fn sha256_block_wires<'a, 'b, FC: MdocHashCompileField, const PLUCKER_WIDTH: usize>(
    allocator: &mut WireAllocator<'a, 'b, FC>,
    plucker: &BitPlucker<'_, CompilerLogic<'b, FC>, PLUCKER_WIDTH>,
) -> circuits_sha256::Derived<CompilerLogic<'b, FC>> {
    let next_plucked =
        |alloc: &mut WireAllocator<'a, 'b, FC>| -> circuits_bitvec::V32<CompilerLogic<'b, FC>> {
            let (unpacked, _) = alloc.allocate_plucked_v32::<PLUCKER_WIDTH>(plucker);
            unpacked
        };

    circuits_sha256::Derived {
        outw: std::array::from_fn(|_| next_plucked(allocator)),
        oute: std::array::from_fn(|_| next_plucked(allocator)),
        outa: std::array::from_fn(|_| next_plucked(allocator)),
        h1: std::array::from_fn(|_| next_plucked(allocator)),
    }
}

pub fn allocate_sha_derived<'b, FC: MdocHashCompileField, const PLUCKER_WIDTH: usize>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    plucker: &BitPlucker<'_, CompilerLogic<'b, FC>, PLUCKER_WIDTH>,
    max_blocks: usize,
) -> Vec<circuits_sha256::Derived<CompilerLogic<'b, FC>>> {
    (0..max_blocks)
        .map(|_| sha256_block_wires(allocator, plucker))
        .collect()
}

pub fn allocate_attr_wires<'a, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'a, FC>,
    plucker_v8: &BitPlucker<'_, CompilerLogic<'a, FC>, { K_HASH_V8_BIT_PLUCKER }>,
    plucker_sha: &BitPlucker<'_, CompilerLogic<'a, FC>, { K_SHA_BIT_PLUCKER }>,
) -> (
    AttrGiven<CompilerLogic<'a, FC>>,
    AttrDerived<CompilerLogic<'a, FC>>,
) {
    let (preimage_value, _) = allocator
        .allocate_plucked_v8_array::<K_ATTR_PREIMAGE_LEN, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);
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
    let sha_derived = allocate_sha_derived(allocator, plucker_sha, K_MAX_ATTR_SHA_BLOCKS);
    let given = AttrGiven {
        preimage,
        mso_digest_offset_in_preimage,
        field_locator,
    };
    let derived = AttrDerived { sha_derived };
    (given, derived)
}

pub fn allocate_pnym_wires<'a, FC: MdocHashCompileField>(
    allocator: &mut WireAllocator<'_, 'a, FC>,
    plucker_v8: &BitPlucker<'_, CompilerLogic<'a, FC>, { K_HASH_V8_BIT_PLUCKER }>,
    plucker_sha: &BitPlucker<'_, CompilerLogic<'a, FC>, { K_SHA_BIT_PLUCKER }>,
) -> (
    PnymGiven<CompilerLogic<'a, FC>>,
    PnymDerived<CompilerLogic<'a, FC>>,
) {
    let (preimage_value, _) = allocator
        .allocate_plucked_v8_array::<K_ATTR_PREIMAGE_LEN, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);
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
    let (pnym_preimage, _) = allocator
        .allocate_plucked_v8_array::<K_PNYM_PREIMAGE_LEN, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);
    let pnym_length_bytes = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();
    let pnym_nblocks = allocator.allocate_bitvec::<2>();

    let item_sha_derived = allocate_sha_derived(allocator, plucker_sha, K_MAX_ATTR_SHA_BLOCKS);
    let pnym_sha_derived = allocate_sha_derived(allocator, plucker_sha, K_PNYM_SHA_BLOCKS);

    let given = PnymGiven {
        preimage,
        mso_digest_offset_in_preimage,
        field_locator,
        pnym_preimage,
        pnym_length_bytes,
        pnym_nblocks,
    };
    let derived = PnymDerived {
        item_sha_derived,
        pnym_sha_derived,
    };
    (given, derived)
}

pub fn allocate_hash<'b, FC>(
    allocator: &mut WireAllocator<'_, 'b, FC>,
    num_attrs: usize,
    pnym: bool,
    plucker_v8: &BitPlucker<'_, CompilerLogic<'b, FC>, { K_HASH_V8_BIT_PLUCKER }>,
    plucker_v256: &BitPlucker<'_, CompilerLogic<'b, FC>, { K_HASH_V256_BIT_PLUCKER }>,
    plucker_sha: &BitPlucker<'_, CompilerLogic<'b, FC>, { K_SHA_BIT_PLUCKER }>,
) -> (
    HashGiven<CompilerLogic<'b, FC>>,
    HashDerived<CompilerLogic<'b, FC>>,
    usize,
    usize,
)
where
    FC: MdocHashCompileField,
{
    let (now, _) = allocator
        .allocate_plucked_v8_array::<K_TIMESTAMP_LEN, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);

    let disclosed_attributes = (0..num_attrs)
        .map(|_| allocate_disclosed_attribute(allocator, plucker_v8))
        .collect();
    let disclosed_pnym = pnym.then(|| allocate_disclosed_pnym(allocator, plucker_v8));

    let mac_e = [allocator.allocate_wire(), allocator.allocate_wire()];
    let mac_device_pkx = [allocator.allocate_wire(), allocator.allocate_wire()];
    let mac_device_pky = [allocator.allocate_wire(), allocator.allocate_wire()];
    let mac_av = allocator.allocate_wire();

    let boolean_io = circuits_boolean::BooleanIO::new(allocator.iologic);
    let suppress_doc_type_check = boolean_io.next(&mut allocator.pos);
    let (expected_doc_type_bytes, _) =
        allocator.allocate_plucked_v8_array::<32, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);
    let expected_doc_type_len = allocator.allocate_bitvec::<{ K_ATTR_INDEX_BITS }>();
    let expected_doc_type = mdoc_zk_circuits::mso_attribute::circuit::AttrSlice {
        data: expected_doc_type_bytes,
        len: expected_doc_type_len,
    };

    let pub_inputs_count = allocator.pos;

    let (issuer_sig_e, _) =
        allocator.allocate_plucked_v256::<{ K_HASH_V256_BIT_PLUCKER }>(plucker_v256);
    let (preimage_value, _) = allocator
        .allocate_plucked_v8_array::<K_MSO_PREIMAGE_LEN, { K_HASH_V8_BIT_PLUCKER }>(plucker_v8);
    let len = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let preimage = MsoPreimageBytes {
        value: preimage_value,
        len,
    };
    let (nblocks, _) = allocator.allocate_plucked_v8::<{ K_HASH_V8_BIT_PLUCKER }>(plucker_v8);

    let (device_pk_x, _) =
        allocator.allocate_plucked_v256::<{ K_HASH_V256_BIT_PLUCKER }>(plucker_v256);
    let (device_pk_y, _) =
        allocator.allocate_plucked_v256::<{ K_HASH_V256_BIT_PLUCKER }>(plucker_v256);
    let device_pk = (device_pk_x, device_pk_y);

    let doc_type_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let valid_from_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let valid_until_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let dev_key_info_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();
    let value_digests_offset_in_preimage = allocator.allocate_bitvec::<K_HASH_INDEX_BITS>();

    let mut attribute_given = Vec::with_capacity(num_attrs);
    let mut attribute_derived = Vec::with_capacity(num_attrs);

    for _ in 0..num_attrs {
        let (given, derived) = allocate_attr_wires(allocator, plucker_v8, plucker_sha);
        attribute_given.push(given);
        attribute_derived.push(derived);
    }

    let (pnym_given, pnym_derived) = if pnym {
        let (pg, pd) = allocate_pnym_wires(allocator, plucker_v8, plucker_sha);
        (Some(pg), Some(pd))
    } else {
        (None, None)
    };

    let sha_derived = allocate_sha_derived(allocator, plucker_sha, K_MAX_SHA_BLOCKS);

    let subfield_boundary_val = allocator.pos;

    let mac_ap = std::array::from_fn(|_| [allocator.allocate_wire(), allocator.allocate_wire()]);

    let given = mdoc_zk_circuits::hash::Given {
        disclosed_attributes,
        disclosed_pnym,
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
        pnym_given,
        mac_e,
        mac_device_pkx,
        mac_device_pky,
        mac_av,
        mac_ap,
    };

    let derived = HashDerived {
        attribute_derived,
        pnym_derived,
        sha_derived,
    };

    (given, derived, pub_inputs_count, subfield_boundary_val)
}
