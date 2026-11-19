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
        bitvec::{BitvecIO, BitvecLogic, V32},
        boolean::BooleanIO,
        sha256msg,
    },
    compile::logic::LogicIO,
    mdoc::{
        circuits::{
            hash::{
                circuit::{AttrGiven, AttrPreimageBytes, Given, MsoPreimageBytes},
                shape::{AttrDerived, Derived},
            },
            mso_attribute::{AttrSlice, DisclosedAttribute, FieldLocator},
        },
        proto::{
            hash::constants::{K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS},
            layout,
            mso_attribute::constants::{
                attr_sha_blocks, attr_value_bytes, K_ATTR_COMPARISON_BITS, K_ATTR_INDEX_BITS,
                K_DATE_SLOT, K_SHA256_BLOCK_SIZE,
            },
        },
    },
};

/// Allocate the complete presentation and return the end of its public prefix.
pub(in crate::mdoc) fn allocate<L: LogicIO>(
    logic: &L,
    num_attrs: usize,
    pos: &mut usize,
) -> (Given<L>, Derived<V32<L>>, usize) {
    let bv = BitvecLogic::new(logic);
    let io = BitvecIO::new(&bv);
    let boolean_io = BooleanIO::new(logic);
    let now = std::array::from_fn(|_| io.next::<8>(pos));
    let disclosed_attributes = (0..num_attrs)
        .map(|slot| DisclosedAttribute {
            expected_name: AttrSlice {
                data: std::array::from_fn(|_| io.next::<8>(pos)),
                len: io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            expected_cbor_value: AttrSlice {
                data: std::array::from_fn(|i| {
                    if i >= attr_value_bytes(slot) {
                        bv.zero()
                    } else {
                        io.next::<8>(pos)
                    }
                }),
                len: io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            enabled: boolean_io.next(pos),
            comparison: (slot == K_DATE_SLOT).then(|| io.next::<K_ATTR_COMPARISON_BITS>(pos)),
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
    // The leading private inputs follow the shared layout table; the runtime
    // link reads the same table, so a drift here must fail compilation.
    let at = |pos: usize, range: &core::ops::Range<usize>, name: &str| {
        if let Err(e) = layout::check_at(pos - npublic, range, name) {
            panic!("{e}");
        }
    };
    // The values shared with the signature circuit come first, in the
    // signature circuit's order, so both circuits store them at the same
    // private offsets.
    at(*pos, &layout::hash::ISSUER_DIGEST, "issuer digest");
    let issuer_sig_e = io.next::<256>(pos);
    at(*pos, &layout::hash::DEVICE_X, "device x");
    let device_x = io.next::<256>(pos);
    at(*pos, &layout::hash::DEVICE_Y, "device y");
    let device_pk = (device_x, io.next::<256>(pos));
    at(*pos, &layout::hash::MSO_PREIMAGE, "MSO preimage");
    let value = std::array::from_fn(|_| io.next::<8>(pos));
    at(*pos, &layout::hash::MSO_LEN, "MSO length");
    let preimage = MsoPreimageBytes {
        value,
        len: io.next::<K_HASH_INDEX_BITS>(pos),
    };
    at(*pos, &layout::hash::NBLOCKS, "block count");
    let nblocks = io.next::<8>(pos);
    at(
        *pos,
        &(layout::hash::NBLOCKS.end..layout::hash::NBLOCKS.end),
        "end of block count",
    );
    let doc_type_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let valid_from_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let valid_until_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let dev_key_info_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let value_digests_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let namespace_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);

    let (attribute_given, attribute_derived) = (0..num_attrs)
        .map(|slot| allocate_attribute(&io, &bv, attr_sha_blocks(slot), pos))
        .unzip();
    let sha_derived = sha256msg::Derived::from_fn(K_MAX_SHA_BLOCKS, || io.next(pos));
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
    io: &BitvecIO<L>,
    bv: &BitvecLogic<L>,
    blocks: usize,
    pos: &mut usize,
) -> (AttrGiven<L>, AttrDerived<V32<L>>) {
    let preimage = AttrPreimageBytes {
        data: std::array::from_fn(|i| {
            if i < blocks * K_SHA256_BLOCK_SIZE {
                io.next::<8>(pos)
            } else {
                bv.zero()
            }
        }),
        len: io.next::<K_ATTR_INDEX_BITS>(pos),
    };
    let mso_digest_offset_in_preimage = io.next::<K_HASH_INDEX_BITS>(pos);
    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|_| io.next::<K_ATTR_INDEX_BITS>(pos)),
        length: std::array::from_fn(|_| io.next::<K_ATTR_INDEX_BITS>(pos)),
        permutation: std::array::from_fn(|_| io.next::<2>(pos)),
    };
    let sha_derived = sha256msg::Derived::from_fn(blocks, || io.next(pos));
    (
        AttrGiven {
            preimage,
            mso_digest_offset_in_preimage,
            field_locator,
        },
        AttrDerived { sha_derived },
    )
}
