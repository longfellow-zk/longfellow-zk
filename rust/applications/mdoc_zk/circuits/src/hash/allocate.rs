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

//! The mdoc witness layout, shared by the application compiler and circuit tests.
//! Public fields come first. Each attribute's private data and SHA witnesses
//! stay adjacent, matching the runtime assignment encoder.
use crate::{
    circuits::{
        bitvec::{BitvecIO, BitvecLogic},
        boolean::BooleanIO,
    },
    compile::logic::LogicIO,
    mdoc::circuits::{
        hash::{
            circuit::{
                AttrDerived, AttrGiven, AttrPreimageBytes, Derived, Given, MsoPreimageBytes,
            },
            constants::{K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS},
        },
        mso_attribute::{
            constants::K_ATTR_INDEX_BITS, AttrSlice, DisclosedAttribute, FieldLocator,
        },
    },
};

/// Allocate the complete presentation and return the end of its public prefix.
pub fn allocate<L: LogicIO>(
    logic: &L,
    num_attrs: usize,
    pos: &mut usize,
) -> (Given<L>, Derived<L>, usize) {
    let bv = BitvecLogic::new(logic);
    let io = BitvecIO::new(&bv);
    let boolean_io = BooleanIO::new(logic);
    let now = std::array::from_fn(|_| io.next::<8>(pos));
    let disclosed_attributes = (0..num_attrs)
        .map(|_| DisclosedAttribute {
            expected_name: AttrSlice {
                data: std::array::from_fn(|_| io.next::<8>(pos)),
                len: io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            expected_cbor_value: AttrSlice {
                data: std::array::from_fn(|_| io.next::<8>(pos)),
                len: io.next::<K_ATTR_INDEX_BITS>(pos),
            },
        })
        .collect();
    let suppress_doc_type_check = boolean_io.next(pos);
    let expected_doc_type = AttrSlice {
        data: std::array::from_fn(|_| io.next::<8>(pos)),
        len: io.next::<K_ATTR_INDEX_BITS>(pos),
    };
    let expected_namespace = AttrSlice {
        data: std::array::from_fn(|_| io.next::<8>(pos)),
        len: io.next::<K_ATTR_INDEX_BITS>(pos),
    };
    let npublic = *pos;
    let issuer_sig_e = io.next::<256>(pos);
    let preimage = MsoPreimageBytes {
        value: std::array::from_fn(|_| io.next::<8>(pos)),
        len: io.next::<K_HASH_INDEX_BITS>(pos),
    };
    let nblocks = io.next::<8>(pos);
    let device_pk = (io.next::<256>(pos), io.next::<256>(pos));
    let doc_type_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let valid_from_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let valid_until_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let dev_key_info_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let value_digests_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let namespace_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);

    let (attribute_given, attribute_derived) = (0..num_attrs)
        .map(|_| allocate_attribute(&bv, &io, pos))
        .unzip();
    let sha_derived = crate::circuits::sha256msg::allocate_derived::<_, K_MAX_SHA_BLOCKS>(&bv, pos);
    (
        Given {
            disclosed_attributes,
            now,
            suppress_doc_type_check,
            expected_doc_type,
            expected_namespace,
            preimage,
            nblocks,
            issuer_sig_e,
            device_pk,
            doc_type_offset_in_preimage,
            valid_from_offset_in_preimage,
            valid_until_offset_in_preimage,
            dev_key_info_offset_in_preimage,
            value_digests_offset_in_preimage,
            namespace_offset_in_preimage,
            attribute_given,
        },
        Derived {
            attribute_derived,
            sha_derived,
        },
        npublic,
    )
}

fn allocate_attribute<L: LogicIO>(
    bv: &BitvecLogic<L>,
    io: &BitvecIO<L>,
    pos: &mut usize,
) -> (AttrGiven<L>, AttrDerived<L>) {
    let preimage = AttrPreimageBytes {
        data: std::array::from_fn(|_| io.next::<8>(pos)),
        len: io.next::<K_ATTR_INDEX_BITS>(pos),
    };
    let mso_digest_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|_| io.next::<K_ATTR_INDEX_BITS>(pos)),
        length: std::array::from_fn(|_| io.next::<K_ATTR_INDEX_BITS>(pos)),
        permutation: std::array::from_fn(|_| io.next::<2>(pos)),
    };
    let sha_derived = crate::circuits::sha256msg::allocate_derived::<_, 2>(bv, pos);
    (
        AttrGiven {
            preimage,
            mso_digest_offset_in_preimage,
            field_locator,
        },
        AttrDerived { sha_derived },
    )
}
