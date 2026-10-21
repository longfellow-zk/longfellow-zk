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

use circuits_bitvec::BitvecLogic;
use core_algebra::Nat;

use super::{
    circuit::{
        AttrDerived as WireAttrDerived, AttrGiven as WireAttrGiven,
        AttrPreimageBytes as WireAttrPreimageBytes, AttrVarSlice as WireAttrVarSlice,
        Derived as WireDerived, DisclosedAttribute as WireDisclosedAttribute, Given as WireGiven,
        MsoPreimageBytes as WireMsoPreimageBytes,
        PnymAttrPreimageBytes as WirePnymAttrPreimageBytes, PnymDerived as WirePnymDerived,
        PnymGiven as WirePnymGiven,
    },
    concrete::{ConcreteDerived, ConcreteGiven},
    constants::K_HASH_INDEX_BITS,
};
use crate::mso_attribute::{
    circuit::{AttrSlice as MsoSlice, FieldLocator as WireFieldLocator},
    constants::{
        K_ATTR_INDEX_BITS, K_OP_BITS, K_PNYM_CONTEXT_BITS, attr_preimage_len,
        attr_sha_blocks_for_circuit, max_attr_val_len,
    },
    pnym::{ContextSlice, DisclosedPnym as WireDisclosedPnym},
};

fn eval_mac_gf128<L: compile_logic::LogicIO>(bv: &BitvecLogic<L>, val: u128) -> L::Wire {
    let boolean = circuits_boolean::Boolean::new(bv.logic());
    let v128 = bv.from_fn::<128, _>(|idx| {
        let bit_val = (val.checked_shr(idx as u32).unwrap_or(0) & 1) == 1;
        boolean.konst(bit_val)
    });
    bv.as_eltw_field(&v128)
}

pub fn evaluate_given<L: compile_logic::LogicIO>(
    logic: &L,
    bv: &BitvecLogic<L>,
    given: &ConcreteGiven,
) -> WireGiven<L> {
    let boolean = circuits_boolean::Boolean::new(logic);
    let num_attr_sha_blocks = attr_sha_blocks_for_circuit(
        given.hash_input.attrs.len(),
        given.hash_input.pnym.is_some(),
    );
    let val_len = max_attr_val_len(num_attr_sha_blocks);
    let preimage_len = attr_preimage_len(num_attr_sha_blocks);

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
            expected_cbor_value: WireAttrVarSlice {
                data: (0..val_len)
                    .map(|i| {
                        let bit_val = get_byte(&a.expected_cbor_value, i);
                        bv.of_u64::<8>(u64::from(bit_val))
                    })
                    .collect(),
                len: bv.of_u64::<K_ATTR_INDEX_BITS>(a.expected_cbor_value.len() as u64),
            },
            op: bv.of_u64::<K_OP_BITS>(u64::from(a.op)),
        })
        .collect();

    let disclosed_pnym = given.hash_input.pnym.as_ref().map(|p| WireDisclosedPnym {
        expected_name: MsoSlice {
            data: std::array::from_fn(|i| {
                let bit_val = get_byte(&p.expected_name, i);
                bv.of_u64::<8>(u64::from(bit_val))
            }),
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(p.expected_name.len() as u64),
        },
        expected_cbor_value: MsoSlice {
            data: std::array::from_fn(|i| {
                let bit_val = get_byte(&p.expected_cbor_value, i);
                bv.of_u64::<8>(u64::from(bit_val))
            }),
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(p.expected_cbor_value.len() as u64),
        },
        context: ContextSlice {
            data: std::array::from_fn(|i| {
                let bit_val = get_byte(&p.context, i);
                bv.of_u64::<8>(u64::from(bit_val))
            }),
            len: bv.of_u64::<K_PNYM_CONTEXT_BITS>(p.context.len() as u64),
        },
    });

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
                data: (0..preimage_len)
                    .map(|i| {
                        let bit_val = get_byte(&a.padded_preimage, i);
                        bv.of_u64::<8>(u64::from(bit_val))
                    })
                    .collect(),
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

    let pnym_given = given.pnym_given.as_ref().map(|pg| WirePnymGiven {
        preimage: WirePnymAttrPreimageBytes {
            data: std::array::from_fn(|i| {
                let bit_val = get_byte(&pg.padded_preimage, i);
                bv.of_u64::<8>(u64::from(bit_val))
            }),
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(pg.unpadded_preimage_len as u64),
        },
        mso_digest_offset_in_preimage: bv
            .of_u64::<K_HASH_INDEX_BITS>(pg.mso_digest_offset_in_preimage as u64),
        field_locator: WireFieldLocator {
            slot_position: std::array::from_fn(|j| {
                bv.of_u64::<K_ATTR_INDEX_BITS>(pg.field_locator.slot_position[j] as u64)
            }),
            length: std::array::from_fn(|j| {
                bv.of_u64::<K_ATTR_INDEX_BITS>(pg.field_locator.length[j] as u64)
            }),
            permutation: std::array::from_fn(|j| {
                let slot = (pg.field_locator.permutation >> (2 * j)) & 3;
                bv.of_u64::<2>(slot as u64)
            }),
        },
        pnym_preimage: std::array::from_fn(|i| {
            let bit_val = get_byte(&pg.pnym_padded_preimage, i);
            bv.of_u64::<8>(u64::from(bit_val))
        }),
        pnym_length_bytes: bv.of_u64::<K_ATTR_INDEX_BITS>(pg.pnym_length_bytes as u64),
        pnym_nblocks: bv.of_u64::<2>(pg.pnym_nblocks as u64),
    });

    let mac_e = [
        eval_mac_gf128(bv, given.mac_e[0]),
        eval_mac_gf128(bv, given.mac_e[1]),
    ];
    let mac_device_pkx = [
        eval_mac_gf128(bv, given.mac_device_pkx[0]),
        eval_mac_gf128(bv, given.mac_device_pkx[1]),
    ];
    let mac_device_pky = [
        eval_mac_gf128(bv, given.mac_device_pky[0]),
        eval_mac_gf128(bv, given.mac_device_pky[1]),
    ];

    let mac_av = eval_mac_gf128(bv, given.mac_input.mac_av);

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
        mac_ap: std::array::from_fn(|i| {
            [
                eval_mac_gf128(bv, given.mac_input.mac_ap[i][0]),
                eval_mac_gf128(bv, given.mac_input.mac_ap[i][1]),
            ]
        }),
    }
}

pub fn evaluate_derived<L: compile_logic::LogicIO>(
    _logic: &L,
    bv: &BitvecLogic<L>,
    derived: &ConcreteDerived,
) -> WireDerived<L> {
    let mut attribute_derived = Vec::with_capacity(derived.attribute_derived.len());
    for a in &derived.attribute_derived {
        let sha_derived = circuits_sha256msg::evaluate::evaluate_derived(&a.sha_derived, bv);
        attribute_derived.push(WireAttrDerived { sha_derived });
    }

    let pnym_derived = derived.pnym_derived.as_ref().map(|pd| WirePnymDerived {
        item_sha_derived: circuits_sha256msg::evaluate::evaluate_derived(&pd.item_sha_derived, bv),
        pnym_sha_derived: circuits_sha256msg::evaluate::evaluate_derived(&pd.pnym_sha_derived, bv),
    });

    let sha_derived = circuits_sha256msg::evaluate::evaluate_derived(&derived.sha_derived, bv);

    WireDerived {
        attribute_derived,
        pnym_derived,
        sha_derived,
    }
}
