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

use circuits_bitvec::{BitvecIO, BitvecLogic};
use circuits_boolean::BooleanIO;
use compile_logic::LogicIO;

use crate::{
    hash::{
        circuit::{
            AttrDerived, AttrGiven, AttrPreimageBytes, AttrVarSlice, Derived, DisclosedAttribute,
            Given, MsoPreimageBytes, PnymAttrPreimageBytes, PnymDerived, PnymGiven,
        },
        constants::{K_HASH_INDEX_BITS, K_TIMESTAMP_LEN},
    },
    mso_attribute::{
        constants::{
            K_ATTR_INDEX_BITS, K_LARGE_ATTR_SHA_BLOCKS, K_MAX_ATTR_SHA_BLOCKS, K_OP_BITS,
            K_PNYM_CONTEXT_BITS, K_PNYM_SHA_BLOCKS, attr_preimage_len, attr_sha_blocks_for_circuit,
            max_attr_val_len,
        },
        pnym::{ContextSlice, DisclosedPnym},
    },
};

pub fn allocate_given<L: LogicIO>(
    logic: &L,
    bv: &BitvecLogic<L>,
    num_attrs: usize,
    pos: &mut usize,
) -> Given<L> {
    allocate_given_with_pnym(logic, bv, num_attrs, false, pos)
}

pub fn allocate_given_with_pnym<L: LogicIO>(
    logic: &L,
    bv: &BitvecLogic<L>,
    num_attrs: usize,
    pnym: bool,
    pos: &mut usize,
) -> Given<L> {
    let bitvec_io = BitvecIO::new(bv);
    let boolean_io = BooleanIO::new(logic);
    let num_attr_sha_blocks = attr_sha_blocks_for_circuit(num_attrs, pnym);
    let val_len = max_attr_val_len(num_attr_sha_blocks);
    let preimage_len = attr_preimage_len(num_attr_sha_blocks);

    let disclosed_attributes = (0..num_attrs)
        .map(|_| DisclosedAttribute {
            expected_name: crate::mso_attribute::circuit::AttrSlice {
                data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
                len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            expected_cbor_value: AttrVarSlice {
                data: (0..val_len).map(|_| bitvec_io.next::<8>(pos)).collect(),
                len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            op: bitvec_io.next::<K_OP_BITS>(pos),
        })
        .collect();

    let disclosed_pnym = pnym.then(|| DisclosedPnym {
        expected_name: crate::mso_attribute::circuit::AttrSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        },
        expected_cbor_value: crate::mso_attribute::circuit::AttrSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        },
        context: ContextSlice {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_PNYM_CONTEXT_BITS>(pos),
        },
    });

    let now: [circuits_bitvec::V8<L>; K_TIMESTAMP_LEN] =
        std::array::from_fn(|_| bitvec_io.next::<8>(pos));

    let mac_e = [logic.next(pos), logic.next(pos)];
    let mac_device_pkx = [logic.next(pos), logic.next(pos)];
    let mac_device_pky = [logic.next(pos), logic.next(pos)];
    let mac_av = logic.next(pos);

    let suppress_doc_type_check = boolean_io.next(pos);

    let expected_doc_type = crate::mso_attribute::circuit::AttrSlice {
        data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
        len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
    };

    let issuer_sig_e = bitvec_io.next::<256>(pos);
    let preimage = MsoPreimageBytes {
        value: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
        len: bitvec_io.next::<K_HASH_INDEX_BITS>(pos),
    };
    let nblocks = bitvec_io.next::<8>(pos);
    let device_pk = (bitvec_io.next::<256>(pos), bitvec_io.next::<256>(pos));
    let doc_type_offset_in_preimage = bitvec_io.next::<16>(pos);
    let valid_from_offset_in_preimage = bitvec_io.next::<16>(pos);
    let valid_until_offset_in_preimage = bitvec_io.next::<16>(pos);
    let dev_key_info_offset_in_preimage = bitvec_io.next::<16>(pos);
    let value_digests_offset_in_preimage = bitvec_io.next::<16>(pos);

    let attribute_given = (0..num_attrs)
        .map(|_| AttrGiven {
            preimage: AttrPreimageBytes {
                data: (0..preimage_len)
                    .map(|_| bitvec_io.next::<8>(pos))
                    .collect(),
                len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
            },
            mso_digest_offset_in_preimage: bitvec_io.next::<16>(pos),
            field_locator: crate::mso_attribute::FieldLocator {
                slot_position: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
                length: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
                permutation: std::array::from_fn(|_| bitvec_io.next::<2>(pos)),
            },
        })
        .collect();

    let pnym_given = pnym.then(|| PnymGiven {
        preimage: PnymAttrPreimageBytes {
            data: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
            len: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        },
        mso_digest_offset_in_preimage: bitvec_io.next::<16>(pos),
        field_locator: crate::mso_attribute::FieldLocator {
            slot_position: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
            length: std::array::from_fn(|_| bitvec_io.next::<K_ATTR_INDEX_BITS>(pos)),
            permutation: std::array::from_fn(|_| bitvec_io.next::<2>(pos)),
        },
        pnym_preimage: std::array::from_fn(|_| bitvec_io.next::<8>(pos)),
        pnym_length_bytes: bitvec_io.next::<K_ATTR_INDEX_BITS>(pos),
        pnym_nblocks: bitvec_io.next::<2>(pos),
    });

    let mac_ap = std::array::from_fn(|_| [logic.next(pos), logic.next(pos)]);

    Given {
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
    }
}

pub fn allocate_derived<L: LogicIO, const MAX_MSO_BLOCKS: usize>(
    bv: &BitvecLogic<L>,
    num_attrs: usize,
    pos: &mut usize,
) -> Derived<L> {
    allocate_derived_with_pnym::<L, MAX_MSO_BLOCKS>(bv, num_attrs, false, pos)
}

pub fn allocate_derived_with_pnym<L: LogicIO, const MAX_MSO_BLOCKS: usize>(
    bv: &BitvecLogic<L>,
    num_attrs: usize,
    pnym: bool,
    pos: &mut usize,
) -> Derived<L> {
    let num_attr_sha_blocks = attr_sha_blocks_for_circuit(num_attrs, pnym);
    let attribute_derived = (0..num_attrs)
        .map(|_| AttrDerived {
            sha_derived: if num_attr_sha_blocks == K_LARGE_ATTR_SHA_BLOCKS {
                circuits_sha256msg::allocate_derived::<_, K_LARGE_ATTR_SHA_BLOCKS>(bv, pos)
            } else {
                circuits_sha256msg::allocate_derived::<_, K_MAX_ATTR_SHA_BLOCKS>(bv, pos)
            },
        })
        .collect();

    let pnym_derived = pnym.then(|| PnymDerived {
        item_sha_derived: circuits_sha256msg::allocate_derived::<_, K_MAX_ATTR_SHA_BLOCKS>(bv, pos),
        pnym_sha_derived: circuits_sha256msg::allocate_derived::<_, K_PNYM_SHA_BLOCKS>(bv, pos),
    });

    let sha_derived = circuits_sha256msg::allocate_derived::<_, MAX_MSO_BLOCKS>(bv, pos);

    Derived {
        attribute_derived,
        pnym_derived,
        sha_derived,
    }
}
