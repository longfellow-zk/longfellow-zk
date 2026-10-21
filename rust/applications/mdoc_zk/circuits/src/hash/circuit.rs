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

use circuits_bitvec::{Bitvec, BitvecLogic, V256, V8};
use circuits_boolean::Boolean;
use circuits_memcmp::Memcmp;
use circuits_routing::Routing;
use circuits_sha256msg::Sha256Msg;
use compile_logic::{Logic, LogicIO};

use super::constants::{
    K_DEVICE_KEY_INFO_CHECK_CBOR, K_DOCTYPE_HEADER_CHECK_CBOR, K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS,
    K_MSO_PREIMAGE_LEN, K_TAG32, K_VALID_FROM_CHECK_CBOR, K_VALID_FROM_LEN,
    K_VALID_UNTIL_CHECK_CBOR, K_VALID_UNTIL_LEN, K_VALUE_DIGESTS_CHECK_CBOR,
};
use crate::{
    hash::constants::K_TIMESTAMP_LEN,
    mso_attribute::{
        circuit::{AttrIndex, AttributeVerifier},
        constants::{
            K_ATTR_PREIMAGE_LEN, K_LARGE_ATTR_SHA_BLOCKS, K_LARGE_ATTR_VAL_LEN,
            K_MAX_ATTR_SHA_BLOCKS, K_MAX_ATTR_VAL_LEN, K_OP_BITS, K_PNYM_PREIMAGE_LEN,
            attr_sha_blocks_for_circuit,
        },
        pnym::{DisclosedPnym, PnymAttributeVerifier},
    },
    traits::MdocHashCompileField,
};

pub type HashIndex<L> = Bitvec<L, K_HASH_INDEX_BITS>;

#[derive(Clone)]
pub struct HashBytes<L: Logic, const N: usize> {
    pub value: [V8<L>; N],
    pub len: HashIndex<L>,
}

pub struct AttrVarSlice<L: Logic> {
    pub data: Vec<V8<L>>,
    pub len: AttrIndex<L>,
}

impl<L: Logic> Clone for AttrVarSlice<L> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            len: self.len.clone(),
        }
    }
}

pub type AttrPreimageBytes<L> = AttrVarSlice<L>;
pub type PnymAttrPreimageBytes<L> =
    crate::mso_attribute::circuit::AttrSlice<L, K_ATTR_PREIMAGE_LEN>;
pub type MsoPreimageBytes<L> = HashBytes<L, K_MSO_PREIMAGE_LEN>;

pub struct DisclosedAttribute<L: Logic> {
    pub expected_name: crate::mso_attribute::circuit::AttrSlice<L, 32>,
    pub expected_cbor_value: AttrVarSlice<L>,
    pub op: Bitvec<L, K_OP_BITS>,
}

impl<L: Logic> Clone for DisclosedAttribute<L> {
    fn clone(&self) -> Self {
        Self {
            expected_name: self.expected_name.clone(),
            expected_cbor_value: self.expected_cbor_value.clone(),
            op: self.op.clone(),
        }
    }
}

pub struct AttrGiven<L: Logic> {
    pub preimage: AttrPreimageBytes<L>,
    pub mso_digest_offset_in_preimage: HashIndex<L>,
    pub field_locator: crate::mso_attribute::FieldLocator<L>,
}

pub struct AttrDerived<L: Logic> {
    pub sha_derived: circuits_sha256msg::Derived<L>,
}

pub struct PnymGiven<L: Logic> {
    pub preimage: PnymAttrPreimageBytes<L>,
    pub mso_digest_offset_in_preimage: HashIndex<L>,
    pub field_locator: crate::mso_attribute::FieldLocator<L>,
    pub pnym_preimage: [V8<L>; K_PNYM_PREIMAGE_LEN],
    pub pnym_length_bytes: AttrIndex<L>,
    pub pnym_nblocks: Bitvec<L, 2>,
}

pub type PnymDerived<L> = crate::mso_attribute::pnym::Derived<L>;

pub struct Given<L: LogicIO> {
    pub disclosed_attributes: Vec<DisclosedAttribute<L>>,
    pub disclosed_pnym: Option<DisclosedPnym<L>>,
    pub now: [V8<L>; K_TIMESTAMP_LEN],
    pub suppress_doc_type_check: circuits_boolean::Bitw<L>,
    pub expected_doc_type: crate::mso_attribute::circuit::AttrSlice<L, 32>,
    pub preimage: MsoPreimageBytes<L>,
    pub nblocks: V8<L>,
    pub issuer_sig_e: V256<L>,
    pub device_pk: (V256<L>, V256<L>),
    pub doc_type_offset_in_preimage: HashIndex<L>,
    pub valid_from_offset_in_preimage: HashIndex<L>,
    pub valid_until_offset_in_preimage: HashIndex<L>,
    pub dev_key_info_offset_in_preimage: HashIndex<L>,
    pub value_digests_offset_in_preimage: HashIndex<L>,
    pub attribute_given: Vec<AttrGiven<L>>,
    pub pnym_given: Option<PnymGiven<L>>,
    pub mac_e: [L::Wire; 2],
    pub mac_device_pkx: [L::Wire; 2],
    pub mac_device_pky: [L::Wire; 2],
    pub mac_av: L::Wire,
    pub mac_ap: [[L::Wire; 2]; 3],
}

pub struct Derived<L: LogicIO> {
    pub attribute_derived: Vec<AttrDerived<L>>,
    pub pnym_derived: Option<PnymDerived<L>>,
    pub sha_derived: circuits_sha256msg::Derived<L>,
}

pub struct MdocHash<'a, L: LogicIO>
where L::F: MdocHashCompileField
{
    pub(crate) logic: &'a L,
    pub(crate) mac_circuit: circuits_mac_gf128::circuit::MAC<'a, L>,
    pub(crate) shamsg_mso: Sha256Msg<'a, L, K_MAX_SHA_BLOCKS>,
    pub(crate) routing: Routing<'a, L>,
    pub(crate) boolean: Boolean<'a, L>,
    pub(crate) bv: BitvecLogic<'a, L>,
    pub(crate) cmp_helper: Memcmp<'a, L>,
    pub(crate) attribute_verifier:
        AttributeVerifier<'a, L, K_MAX_ATTR_SHA_BLOCKS, K_MAX_ATTR_VAL_LEN>,
    pub(crate) large_attribute_verifier:
        AttributeVerifier<'a, L, K_LARGE_ATTR_SHA_BLOCKS, K_LARGE_ATTR_VAL_LEN>,
    pub(crate) num_attr_sha_blocks: usize,
    pub(crate) pnym_verifier: Option<PnymAttributeVerifier<'a, L>>,
}

impl<'a, L: LogicIO> MdocHash<'a, L>
where L::F: MdocHashCompileField
{
    pub fn new(logic: &'a L, num_attrs: usize) -> Self {
        Self::with_pnym(logic, num_attrs, false)
    }

    pub fn with_pnym(logic: &'a L, num_attrs: usize, pnym: bool) -> Self {
        Self {
            logic,
            mac_circuit: circuits_mac_gf128::circuit::MAC::new(logic),
            shamsg_mso: Sha256Msg::new(logic),
            routing: Routing::new(logic),
            boolean: Boolean::new(logic),
            bv: BitvecLogic::new(logic),
            cmp_helper: Memcmp::new(logic),
            attribute_verifier: AttributeVerifier::new(logic),
            large_attribute_verifier: AttributeVerifier::with_size(logic),
            num_attr_sha_blocks: attr_sha_blocks_for_circuit(num_attrs, pnym),
            pnym_verifier: pnym.then(|| PnymAttributeVerifier::new(logic)),
        }
    }

    pub fn assert_valid_presentation(
        &self,
        given: &Given<L>,
        derived: &Derived<L>,
    ) -> L::Assertions {
        assert_eq!(
            given.disclosed_attributes.len(),
            derived.attribute_derived.len(),
            "Mismatched number of disclosed attributes and attribute derived structures"
        );
        let preimage = given.preimage.value.to_vec();

        let mut assertions = vec![
            self.assert_mso_sha256_hash(given, derived, &preimage),
            self.assert_mso_doc_type(given, &preimage),
            self.assert_mso_validity(given, &preimage),
            self.assert_mso_device_key(given, &preimage),
            self.assert_mso_value_digests(given, &preimage),
            self.assert_attributes(given, derived, &preimage),
        ];
        if let Some(ref pnym_verifier) = self.pnym_verifier {
            assertions.push(self.assert_pnym(pnym_verifier, given, derived, &preimage));
        }

        self.logic
            .assert_all("assert_valid_presentation", &assertions)
    }

    fn assert_mso_sha256_hash(
        &self,
        given: &Given<L>,
        derived: &Derived<L>,
        preimage: &[V8<L>],
    ) -> L::Assertions {
        let preimage_len_64 = self
            .bv
            .zext::<{ K_HASH_INDEX_BITS }, 64>(&given.preimage.len);
        let nblocks_ext = self.bv.zext::<8, { K_MAX_SHA_BLOCKS }>(&given.nblocks);

        let shamsg_given = circuits_sha256msg::circuit::Given {
            padded_preimage: preimage.to_vec(),
            nblocks: nblocks_ext,
            length_bytes: preimage_len_64,
            expected_hash: given.issuer_sig_e.clone(),
        };

        self.shamsg_mso
            .assert_message_hash(&shamsg_given, &derived.sha_derived)
    }

    pub fn assert_valid_presentation_and_macs(
        &self,
        given: &Given<L>,
        derived: &Derived<L>,
    ) -> L::Assertions {
        self.logic.assert_all(
            "assert_valid_presentation_and_macs",
            &[
                self.assert_valid_presentation(given, derived),
                self.assert_mac_tags(given),
            ],
        )
    }

    fn assert_mac_tags(&self, given: &Given<L>) -> L::Assertions {
        self.logic.assert_all(
            "assert_mac_tags",
            &[
                self.mac_circuit.assert_mac(&circuits_mac_gf128::Given {
                    message: given.issuer_sig_e.clone(),
                    mac_av: given.mac_av.clone(),
                    mac_ap: given.mac_ap[0].clone(),
                    tag: given.mac_e.clone(),
                }),
                self.mac_circuit.assert_mac(&circuits_mac_gf128::Given {
                    message: given.device_pk.0.clone(),
                    mac_av: given.mac_av.clone(),
                    mac_ap: given.mac_ap[1].clone(),
                    tag: given.mac_device_pkx.clone(),
                }),
                self.mac_circuit.assert_mac(&circuits_mac_gf128::Given {
                    message: given.device_pk.1.clone(),
                    mac_av: given.mac_av.clone(),
                    mac_ap: given.mac_ap[2].clone(),
                    tag: given.mac_device_pky.clone(),
                }),
            ],
        )
    }

    fn assert_mso_doc_type(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let zz = self.bv.zero::<8>();

        let (doc_type_shifted, shift_assertions) = self.shift_preimage(
            &given.doc_type_offset_in_preimage,
            &given.preimage.len,
            7,
            K_DOCTYPE_HEADER_CHECK_CBOR.len() + 35,
            preimage,
            &zz,
        );

        let header_check =
            self.logic
                .assert_mapi("cbor_header", 0..K_DOCTYPE_HEADER_CHECK_CBOR.len(), |i| {
                    let eq_bit = self.bv.eqb(
                        &doc_type_shifted[i],
                        &self.bv.of_u8(K_DOCTYPE_HEADER_CHECK_CBOR[i]),
                    );
                    let cond_eq = self.boolean.orb(&given.suppress_doc_type_check, &eq_bit);
                    self.boolean.assert_true("header_byte", &cond_eq)
                });

        let head_byte = &doc_type_shifted[K_DOCTYPE_HEADER_CHECK_CBOR.len()];
        let is_two_byte_header = self.bv.eqb(head_byte, &self.bv.of_u8(0x78));

        let value_check = self.logic.assert_mapi("value_bytes", 0..32, |i| {
            let i_wire = self
                .bv
                .of_u64::<{ crate::mso_attribute::constants::K_ATTR_INDEX_BITS }>(i as u64);
            let in_bounds = self.bv.lt(&i_wire, &given.expected_doc_type.len);
            let active = self.boolean.andb(
                &self.boolean.notb(&given.suppress_doc_type_check),
                &in_bounds,
            );

            let byte_if_1 = &doc_type_shifted[K_DOCTYPE_HEADER_CHECK_CBOR.len() + 1 + i];
            let byte_if_2 = &doc_type_shifted[K_DOCTYPE_HEADER_CHECK_CBOR.len() + 2 + i];
            let got = self
                .bv
                .select::<8>(&is_two_byte_header, byte_if_2, byte_if_1);

            let want = &given.expected_doc_type.data[i];
            let eq_bit = self.bv.eqb(&got, want);
            let cond_eq = self.boolean.impliesb(&active, &eq_bit);
            self.boolean.assert_true("doc_type_byte", &cond_eq)
        });

        self.logic.assert_all(
            "assert_mso_doc_type",
            &[shift_assertions, header_check, value_check],
        )
    }

    fn assert_mso_validity(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let zz = self.bv.zero::<8>();

        let (valid_from_shifted, from_assertions) = self.shift_preimage(
            &given.valid_from_offset_in_preimage,
            &given.preimage.len,
            3,
            K_VALID_FROM_LEN + K_TIMESTAMP_LEN,
            preimage,
            &zz,
        );
        let cmp_from = self.cmp_helper.leq(
            &valid_from_shifted[K_VALID_FROM_LEN..K_VALID_FROM_LEN + K_TIMESTAMP_LEN],
            &given.now,
        );

        let (valid_until_shifted, until_assertions) = self.shift_preimage(
            &given.valid_until_offset_in_preimage,
            &given.preimage.len,
            3,
            K_VALID_UNTIL_LEN + K_TIMESTAMP_LEN,
            preimage,
            &zz,
        );
        let cmp_until = self.cmp_helper.leq(
            &given.now,
            &valid_until_shifted[K_VALID_UNTIL_LEN..K_VALID_UNTIL_LEN + K_TIMESTAMP_LEN],
        );

        let from_assertion = self.logic.assert_all(
            "valid_from",
            &[
                from_assertions,
                self.assert_bytes_at(
                    K_VALID_FROM_LEN,
                    &valid_from_shifted[0..K_VALID_FROM_LEN],
                    &K_VALID_FROM_CHECK_CBOR,
                ),
                self.boolean.assert_true("cmp_from", &cmp_from),
            ],
        );

        let until_assertion = self.logic.assert_all(
            "valid_until",
            &[
                until_assertions,
                self.assert_bytes_at(
                    K_VALID_UNTIL_LEN,
                    &valid_until_shifted[0..K_VALID_UNTIL_LEN],
                    &K_VALID_UNTIL_CHECK_CBOR,
                ),
                self.boolean.assert_true("cmp_until", &cmp_until),
            ],
        );

        self.logic
            .assert_all("assert_mso_validity", &[from_assertion, until_assertion])
    }

    fn assert_mso_device_key(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let zz = self.bv.zero::<8>();

        let (dev_key_info_shifted, shift_assertions) = self.shift_preimage(
            &given.dev_key_info_offset_in_preimage,
            &given.preimage.len,
            4,
            K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32 + 3 + 32,
            preimage,
            &zz,
        );
        let dpky_check = [0x22, 0x58, 0x20];

        self.logic.assert_all(
            "assert_mso_device_key",
            &[
                shift_assertions,
                self.assert_bytes_at(
                    K_DEVICE_KEY_INFO_CHECK_CBOR.len(),
                    &dev_key_info_shifted[0..K_DEVICE_KEY_INFO_CHECK_CBOR.len()],
                    &K_DEVICE_KEY_INFO_CHECK_CBOR,
                ),
                self.assert_key(
                    &given.device_pk.0,
                    &dev_key_info_shifted[K_DEVICE_KEY_INFO_CHECK_CBOR.len()
                        ..K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32],
                ),
                self.assert_bytes_at(
                    3,
                    &dev_key_info_shifted[K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32
                        ..K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32 + 3],
                    &dpky_check,
                ),
                self.assert_key(
                    &given.device_pk.1,
                    &dev_key_info_shifted[K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32 + 3
                        ..K_DEVICE_KEY_INFO_CHECK_CBOR.len() + 32 + 3 + 32],
                ),
            ],
        )
    }

    fn assert_mso_value_digests(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let zz = self.bv.zero::<8>();

        let (value_digests_shifted, shift_assertions) = self.shift_preimage(
            &given.value_digests_offset_in_preimage,
            &given.preimage.len,
            4,
            K_VALUE_DIGESTS_CHECK_CBOR.len(),
            preimage,
            &zz,
        );
        self.logic.assert_all(
            "assert_mso_value_digests",
            &[
                shift_assertions,
                self.assert_bytes_at(
                    K_VALUE_DIGESTS_CHECK_CBOR.len(),
                    &value_digests_shifted[0..K_VALUE_DIGESTS_CHECK_CBOR.len()],
                    &K_VALUE_DIGESTS_CHECK_CBOR,
                ),
            ],
        )
    }

    fn assert_attributes(
        &self,
        given: &Given<L>,
        derived: &Derived<L>,
        preimage: &[V8<L>],
    ) -> L::Assertions {
        let zz = self.bv.zero::<8>();

        self.logic.assert_mapi(
            "assert_attributes",
            0..given.disclosed_attributes.len(),
            |i| {
                let attr_given = &given.attribute_given[i];
                let attr_der = &derived.attribute_derived[i];

                let (mso_digest_shifted, shift_assertions) = self.shift_preimage(
                    &attr_given.mso_digest_offset_in_preimage,
                    &given.preimage.len,
                    3,
                    K_TAG32.len() + 32,
                    preimage,
                    &zz,
                );

                let expected_digest = self.bv.from_fn::<256, _>(|j| {
                    let byte_idx = K_TAG32.len() + (255 - j) / 8;
                    let bit_idx = j % 8;
                    mso_digest_shifted[byte_idx].as_array()[bit_idx].clone()
                });

                let tag32_header_assertion = self.assert_bytes_at(
                    K_TAG32.len(),
                    &mso_digest_shifted[0..K_TAG32.len()],
                    &K_TAG32,
                );

                let da = &given.disclosed_attributes[i];
                let attribute_verifier_assertions =
                    if self.num_attr_sha_blocks == K_LARGE_ATTR_SHA_BLOCKS {
                        self.large_attribute_verifier.assert_attribute_slices(
                            &attr_given.preimage.data,
                            &attr_given.preimage.len,
                            &attr_given.field_locator,
                            &da.expected_name,
                            &da.expected_cbor_value.data,
                            &da.expected_cbor_value.len,
                            &da.op,
                            &expected_digest,
                            &attr_der.sha_derived,
                        )
                    } else {
                        self.attribute_verifier.assert_attribute_slices(
                            &attr_given.preimage.data,
                            &attr_given.preimage.len,
                            &attr_given.field_locator,
                            &da.expected_name,
                            &da.expected_cbor_value.data,
                            &da.expected_cbor_value.len,
                            &da.op,
                            &expected_digest,
                            &attr_der.sha_derived,
                        )
                    };

                self.logic.assert_all(
                    "attribute_item",
                    &[
                        shift_assertions,
                        tag32_header_assertion,
                        attribute_verifier_assertions,
                    ],
                )
            },
        )
    }

    fn assert_pnym(
        &self,
        pnym_verifier: &PnymAttributeVerifier<'a, L>,
        given: &Given<L>,
        derived: &Derived<L>,
        preimage: &[V8<L>],
    ) -> L::Assertions {
        let zz = self.bv.zero::<8>();
        let disclosed_pnym = given
            .disclosed_pnym
            .as_ref()
            .expect("disclosed_pnym must be present when pnym_verifier is enabled");
        let pnym_given = given
            .pnym_given
            .as_ref()
            .expect("pnym_given must be present when pnym_verifier is enabled");
        let pnym_der = derived
            .pnym_derived
            .as_ref()
            .expect("pnym_derived must be present when pnym_verifier is enabled");

        let (mso_digest_shifted, shift_assertions) = self.shift_preimage(
            &pnym_given.mso_digest_offset_in_preimage,
            &given.preimage.len,
            3,
            K_TAG32.len() + 32,
            preimage,
            &zz,
        );

        let expected_digest = self.bv.from_fn::<256, _>(|j| {
            let byte_idx = K_TAG32.len() + (255 - j) / 8;
            let bit_idx = j % 8;
            mso_digest_shifted[byte_idx].as_array()[bit_idx].clone()
        });

        let tag32_header_assertion = self.assert_bytes_at(
            K_TAG32.len(),
            &mso_digest_shifted[0..K_TAG32.len()],
            &K_TAG32,
        );

        let verifier_given = crate::mso_attribute::pnym::Given {
            attribute_preimage: pnym_given.preimage.clone(),
            field_locator: pnym_given.field_locator.clone(),
            disclosed_pnym: disclosed_pnym.clone(),
            expected_digest,
            pnym_preimage: pnym_given.pnym_preimage.clone(),
            pnym_length_bytes: pnym_given.pnym_length_bytes.clone(),
            pnym_nblocks: pnym_given.pnym_nblocks.clone(),
        };
        let pnym_assertions = pnym_verifier.assert_pnym_attribute(&verifier_given, pnym_der);

        self.logic.assert_all(
            "assert_pnym",
            &[shift_assertions, tag32_header_assertion, pnym_assertions],
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn shift_preimage(
        &self,
        offset: &HashIndex<L>,
        preimage_length_bytes: &HashIndex<L>,
        shift_base_bits: usize,
        len_bytes: usize,
        preimage: &[V8<L>],
        zz: &V8<L>,
    ) -> (Vec<V8<L>>, L::Assertions) {
        let five = self.bv.of_u64::<16>(5);
        let ge_five = self.bv.leq(&five, offset);
        let lt = self.bv.lt(offset, preimage_length_bytes);

        let assertions = self.logic.assert_all(
            "shift_preimage_bounds",
            &[
                self.boolean.assert_true("ge_five", &ge_five),
                self.boolean.assert_true("lt", &lt),
            ],
        );

        let shifted = self
            .routing
            .shift_bitvec(shift_base_bits, offset, len_bytes, preimage, zz);

        (shifted, assertions)
    }

    fn assert_bytes_at(&self, len: usize, buf: &[V8<L>], want: &[u8]) -> L::Assertions {
        self.logic.assert_mapi("assert_bytes_at", 0..len, |i| {
            self.bv
                .assert_eq("bytes_at", &buf[i], &self.bv.of_u8(want[i]))
        })
    }

    fn assert_key(&self, key: &V256<L>, buf_be: &[V8<L>]) -> L::Assertions {
        let m_bits = self.bv.from_fn::<256, _>(|i| {
            let byte_idx = 31 - (i / 8);
            let bit_idx = i % 8;
            buf_be[byte_idx].as_array()[bit_idx].clone()
        });

        self.bv.assert_eq("key_eq", &m_bits, key)
    }
}
