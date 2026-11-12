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

use super::constants::{
    K_COSE1_PREFIX, K_COSE1_PREFIX_LEN, K_DEVICE_KEY_INFO_CHECK_CBOR, K_DOCTYPE_HEADER_CHECK_CBOR,
    K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS, K_MSO_PREIMAGE_LEN, K_NAMESPACE_BYTES, K_TAG32,
    K_VALID_FROM_CHECK_CBOR, K_VALID_FROM_LEN, K_VALID_UNTIL_CHECK_CBOR, K_VALID_UNTIL_LEN,
    K_VALUE_DIGESTS_CHECK_CBOR,
};
use crate::{
    circuits::{
        bitvec::{Bitvec, BitvecLogic, V256, V8},
        boolean::Boolean,
        memcmp::Memcmp,
        routing::Routing,
        sha256msg::Sha256Msg,
    },
    compile::logic::{Logic, LogicIO},
    mdoc::circuits::{
        mso_attribute::{
            circuit::AttributeVerifier,
            constants::{K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN},
        },
        traits::MdocHashCompileField,
    },
};

pub type HashIndex<L> = Bitvec<L, K_HASH_INDEX_BITS>;

#[derive(Clone)]
pub struct HashBytes<L: Logic, const N: usize> {
    pub value: [V8<L>; N],
    pub len: HashIndex<L>,
}

#[cfg(test)]
#[path = "../../tests/hash_bounds.rs"]
mod tests;

#[cfg(test)]
#[path = "../../tests/hash_inputs.rs"]
mod input_tests;

pub type AttrPreimageBytes<L> =
    crate::mdoc::circuits::mso_attribute::circuit::AttrSlice<L, K_ATTR_PREIMAGE_LEN>;
pub type MsoPreimageBytes<L> = HashBytes<L, K_MSO_PREIMAGE_LEN>;

pub struct AttrGiven<L: Logic> {
    pub preimage: AttrPreimageBytes<L>,
    pub mso_digest_offset_in_preimage: HashIndex<L>,
    pub field_locator: crate::mdoc::circuits::mso_attribute::FieldLocator<L>,
}

use crate::mdoc::circuits::{
    hash::constants::{K_TIMESTAMP_DIGITS, K_TIMESTAMP_LEN},
    mso_attribute::circuit::DisclosedAttribute,
};

pub struct AttrDerived<L: Logic> {
    pub sha_derived: crate::circuits::sha256msg::Derived<L>,
}

pub struct Given<L: LogicIO> {
    pub disclosed_attributes: Vec<DisclosedAttribute<L>>,
    pub now: [V8<L>; K_TIMESTAMP_DIGITS.len()],
    pub suppress_doc_type_check: crate::circuits::boolean::Bitw<L>,
    pub expected_doc_type: crate::mdoc::circuits::mso_attribute::circuit::AttrSlice<L, 32>,
    pub expected_namespace:
        crate::mdoc::circuits::mso_attribute::circuit::AttrSlice<L, K_NAMESPACE_BYTES>,
    pub preimage: MsoPreimageBytes<L>,
    pub nblocks: V8<L>,
    pub issuer_sig_e: V256<L>,
    pub device_pk: (V256<L>, V256<L>),
    pub doc_type_offset_in_preimage: HashIndex<L>,
    pub valid_from_offset_in_preimage: HashIndex<L>,
    pub valid_until_offset_in_preimage: HashIndex<L>,
    pub dev_key_info_offset_in_preimage: HashIndex<L>,
    pub value_digests_offset_in_preimage: HashIndex<L>,
    pub namespace_offset_in_preimage: HashIndex<L>,
    pub attribute_given: Vec<AttrGiven<L>>,
}

pub struct Derived<L: LogicIO> {
    pub attribute_derived: Vec<AttrDerived<L>>,
    pub sha_derived: crate::circuits::sha256msg::Derived<L>,
}

pub struct MdocHash<'a, L: LogicIO>
where
    L::F: MdocHashCompileField,
{
    pub(in crate::mdoc::circuits) logic: &'a L,
    pub(in crate::mdoc::circuits) shamsg_mso: Sha256Msg<'a, L, K_MAX_SHA_BLOCKS>,
    pub(in crate::mdoc::circuits) routing: Routing<'a, L>,
    pub(in crate::mdoc::circuits) boolean: Boolean<'a, L>,
    pub(in crate::mdoc::circuits) bv: BitvecLogic<'a, L>,
    pub(in crate::mdoc::circuits) cmp_helper: Memcmp<'a, L>,
    pub(in crate::mdoc::circuits) attribute_verifier: AttributeVerifier<'a, L>,
}

impl<'a, L: LogicIO> MdocHash<'a, L>
where
    L::F: MdocHashCompileField,
{
    pub fn new(logic: &'a L, _num_attrs: usize) -> Self {
        Self {
            logic,
            shamsg_mso: Sha256Msg::new(logic),
            routing: Routing::new(logic),
            boolean: Boolean::new(logic),
            bv: BitvecLogic::new(logic),
            cmp_helper: Memcmp::new(logic),
            attribute_verifier: AttributeVerifier::new(logic),
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
        assert_eq!(
            given.attribute_given.len(),
            given.disclosed_attributes.len(),
            "Mismatched number of attribute witnesses and disclosed attributes"
        );
        let preimage = given.preimage.value.to_vec();

        self.logic.assert_all(
            "assert_valid_presentation",
            &[
                self.assert_mso_sha256_hash(given, derived, &preimage),
                self.assert_mso_envelope(given, &preimage),
                self.assert_mso_doc_type(given, &preimage),
                self.assert_mso_namespace(given, &preimage),
                self.assert_mso_validity(given, &preimage),
                self.assert_mso_device_key(given, &preimage),
                self.assert_mso_value_digests(given, &preimage),
                self.assert_attributes(given, derived, &preimage),
            ],
        )
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

        let shamsg_given = crate::circuits::sha256msg::circuit::Given {
            padded_preimage: preimage.to_vec(),
            nblocks: nblocks_ext,
            length_bytes: preimage_len_64,
            expected_hash: given.issuer_sig_e.clone(),
        };

        self.shamsg_mso
            .assert_message_hash(&shamsg_given, &derived.sha_derived)
    }

    fn assert_mso_doc_type(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        self.logic.assert_all(
            "assert_mso_doc_type",
            &self.assert_mso_text(
                &given.doc_type_offset_in_preimage,
                &given.preimage.len,
                &given.expected_doc_type,
                &self.boolean.notb(&given.suppress_doc_type_check),
                &K_DOCTYPE_HEADER_CHECK_CBOR,
                preimage,
            ),
        )
    }

    fn assert_mso_namespace(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        // This proves the exact text occurs in the signed MSO. The private
        // offset is not a proof of CBOR ancestry or digest-map membership.
        let mut checks = self
            .assert_mso_text(
                &given.namespace_offset_in_preimage,
                &given.preimage.len,
                &given.expected_namespace,
                &self.boolean.trueb(),
                &[],
                preimage,
            )
            .to_vec();
        let (header_end, arithmetic) = self.bv.checked_add(
            &self
                .bv
                .zext::<16, 17>(&given.value_digests_offset_in_preimage),
            &self
                .bv
                .of_u64::<17>(K_VALUE_DIGESTS_CHECK_CBOR.len() as u64),
        );
        checks.push(arithmetic);
        checks.push(self.boolean.assert_true(
            "after_value_digests",
            &self.bv.leq(
                &header_end,
                &self.bv.zext::<16, 17>(&given.namespace_offset_in_preimage),
            ),
        ));
        self.logic.assert_all("assert_mso_namespace", &checks)
    }

    fn assert_mso_text<const N: usize>(
        &self,
        offset: &HashIndex<L>,
        preimage_len: &HashIndex<L>,
        expected: &crate::mdoc::circuits::mso_attribute::circuit::AttrSlice<L, N>,
        enabled: &crate::circuits::boolean::Bitw<L>,
        prefix: &[u8],
        preimage: &[V8<L>],
    ) -> [L::Assertions; 5] {
        let zz = self.bv.zero::<8>();
        // Lookahead covers both supported text headers. Only the bytes consumed
        // by the selected header and value must be inside the signed message.
        let shifted = self
            .routing
            .shift_bitvec(7, offset, prefix.len() + N + 2, preimage, &zz);

        let header_check = self.logic.assert_mapi("cbor_header", 0..prefix.len(), |i| {
            let eq_bit = self.bv.eqb(&shifted[i], &self.bv.of_u8(prefix[i]));
            let cond_eq = self.boolean.impliesb(enabled, &eq_bit);
            self.boolean.assert_true("header_byte", &cond_eq)
        });

        let head_byte = &shifted[prefix.len()];
        let is_two_byte_header = self.bv.eqb(head_byte, &self.bv.of_u8(0x78));
        let (short_length, _): (Bitvec<L, 5>, Bitvec<L, 3>) = self.bv.split(head_byte);
        let short_text = self.boolean.andb(
            &self.bv.eqmask(head_byte, 0x60, 0xe0),
            &self.bv.lt(&short_length, &self.bv.of_u64::<5>(24)),
        );
        let text_header = self.boolean.orb(&short_text, &is_two_byte_header);
        let signed_length = self.bv.select(
            &is_two_byte_header,
            &self
                .bv
                .zext::<8, K_ATTR_INDEX_BITS>(&shifted[prefix.len() + 1]),
            &self.bv.zext::<5, K_ATTR_INDEX_BITS>(&short_length),
        );
        let matching_length = self.boolean.andb(
            &self.bv.eqb(&signed_length, &expected.len),
            &self.boolean.notb(&self.bv.is_zero(&expected.len)),
        );
        let length_check = self.boolean.assert_true(
            "text_length",
            &self
                .boolean
                .impliesb(enabled, &self.boolean.andb(&text_header, &matching_length)),
        );
        let capacity_check = self.boolean.assert_true(
            "public_length",
            &self.bv.leq(
                &expected.len,
                &self.bv.of_u64::<K_ATTR_INDEX_BITS>(N as u64),
            ),
        );
        // Check both header sizes in parallel. Selecting the header before
        // propagating carries would put routing, two additions and comparison
        // on one path. Carry-save reduction needs only one final carry chain.
        // The 17-bit words hold a 16-bit offset, the 10-bit public length
        // and either fixed prefix without integer wrap.
        let fits = |header_bytes: u64, name: &str| {
            let wide_offset = self.bv.zext::<16, 17>(offset);
            let length = self.bv.zext::<K_ATTR_INDEX_BITS, 17>(&expected.len);
            let header_length = self.bv.of_u64::<17>(header_bytes);
            let (sum, carry, overflow) = self.bv.carry_save(&wide_offset, &length, &header_length);
            let carry_check = self.boolean.assert_false("carry_overflow", &overflow);
            let (end, sum_check) = self.bv.checked_add(&sum, &carry);
            (
                self.bv.leq(&end, &self.bv.zext::<16, 17>(preimage_len)),
                self.logic.assert_all(name, &[carry_check, sum_check]),
            )
        };
        let (short_fits, short_arithmetic) = fits((prefix.len() + 1) as u64, "short_header");
        let (long_fits, long_arithmetic) = fits((prefix.len() + 2) as u64, "long_header");
        let end_fits = self.boolean.impliesb(
            enabled,
            &self
                .boolean
                .muxb(&is_two_byte_header, &long_fits, &short_fits),
        );
        // Suppression keeps the existing valid-start requirement, without
        // imposing a value length or text header on the suppressed field.
        let shift_assertions = self.assert_preimage_bounds(
            offset,
            preimage_len,
            &end_fits,
            self.logic
                .assert_all("header_ranges", &[short_arithmetic, long_arithmetic]),
        );

        let value_check = self.logic.assert_mapi("value_bytes", 0..N, |i| {
            let i_wire = self.bv.of_u64::<K_ATTR_INDEX_BITS>(i as u64);
            let in_bounds = self.bv.lt(&i_wire, &expected.len);
            let active = self.boolean.andb(enabled, &in_bounds);

            let byte_if_1 = &shifted[prefix.len() + 1 + i];
            let byte_if_2 = &shifted[prefix.len() + 2 + i];
            let got = self
                .bv
                .select::<8>(&is_two_byte_header, byte_if_2, byte_if_1);

            let want = &expected.data[i];
            let eq_bit = self.bv.eqb(&got, want);
            let cond_eq = self.boolean.impliesb(&active, &eq_bit);
            self.boolean.assert_true("text_byte", &cond_eq)
        });

        [
            shift_assertions,
            header_check,
            length_check,
            capacity_check,
            value_check,
        ]
    }

    /// Check the supported Signature1 / tagged-byte-string envelope. This binds
    /// the lengths of the signed payload; it does not establish CBOR ancestry.
    fn assert_mso_envelope(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let outer_length = self
            .bv
            .from_fn::<16, _>(|i| preimage[K_COSE1_PREFIX_LEN + 1 - i / 8][i % 8].clone());
        let inner_length = self
            .bv
            .from_fn::<16, _>(|i| preimage[K_COSE1_PREFIX_LEN + 6 - i / 8][i % 8].clone());
        // The expected total length is already a wire. Check each sum directly
        // with the same primitive used by SHA-256, rather than computing carries.
        // Seventeen bits hold every u16 length plus either fixed prefix, so the
        // wrapping-sum equations here are exact integer equalities.
        let length = self.bv.zext::<16, 17>(&given.preimage.len);
        let adder = crate::circuits::analog_adder::AnalogAdder::new(self.logic);
        let outer_check = adder.assert_wrapping_sum(
            &length,
            &[&[
                self.bv.zext::<16, 17>(&outer_length),
                self.bv.of_u64::<17>((K_COSE1_PREFIX_LEN + 2) as u64),
            ]],
        );
        let inner_check = adder.assert_wrapping_sum(
            &length,
            &[&[
                self.bv.zext::<16, 17>(&inner_length),
                self.bv.of_u64::<17>((K_COSE1_PREFIX_LEN + 7) as u64),
            ]],
        );
        self.logic.assert_all(
            "assert_mso_envelope",
            &[
                self.assert_bytes_at(K_COSE1_PREFIX_LEN, preimage, &K_COSE1_PREFIX),
                self.assert_bytes_at(3, &preimage[K_COSE1_PREFIX_LEN + 2..], &[0xd8, 0x18, 0x59]),
                self.logic.assert_all("outer_length", &[outer_check]),
                self.logic.assert_all("inner_length", &[inner_check]),
                self.boolean.assert_true(
                    "map_type",
                    &self
                        .bv
                        .eqmask(&preimage[K_COSE1_PREFIX_LEN + 7], 0xa0, 0xe0),
                ),
            ],
        )
    }

    fn assert_mso_validity(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let zz = self.bv.zero::<8>();
        // Well-formed 20-byte UTC dates sort by their digits. Separators have
        // no ordering meaning, and RFC 3339 permits both T/t and Z/z.
        let digits = |timestamp: &[V8<L>]| K_TIMESTAMP_DIGITS.map(|i| timestamp[i].clone());

        let (valid_from_shifted, from_assertions) = self.shift_preimage(
            &given.valid_from_offset_in_preimage,
            &given.preimage.len,
            3,
            K_VALID_FROM_LEN + K_TIMESTAMP_LEN,
            preimage,
            &zz,
        );
        let cmp_from = self.cmp_helper.leq(
            &digits(&valid_from_shifted[K_VALID_FROM_LEN..K_VALID_FROM_LEN + K_TIMESTAMP_LEN]),
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
            &digits(&valid_until_shifted[K_VALID_UNTIL_LEN..K_VALID_UNTIL_LEN + K_TIMESTAMP_LEN]),
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

                let verifier_given = crate::mdoc::circuits::mso_attribute::circuit::Given {
                    attribute_preimage: attr_given.preimage.clone(),
                    field_locator: attr_given.field_locator.clone(),
                    disclosed_attribute: given.disclosed_attributes[i].clone(),
                    expected_digest,
                };
                let attribute_verifier_assertions = self
                    .attribute_verifier
                    .assert_attribute(&verifier_given, &attr_der.sha_derived);

                self.logic.assert_all(
                    "attribute_item",
                    &[
                        shift_assertions,
                        tag32_header_assertion,
                        self.assert_namespace_before_digest(
                            given,
                            &attr_given.mso_digest_offset_in_preimage,
                        ),
                        attribute_verifier_assertions,
                    ],
                )
            },
        )
    }

    // These ordering checks exclude header aliases and backwards splices;
    // they do not establish general CBOR map ancestry.
    fn assert_namespace_before_digest(
        &self,
        given: &Given<L>,
        digest: &HashIndex<L>,
    ) -> L::Assertions {
        let (text_end, arithmetic) = self.bv.checked_add(
            &self.bv.zext::<16, 17>(&given.namespace_offset_in_preimage),
            &self
                .bv
                .zext::<K_ATTR_INDEX_BITS, 17>(&given.expected_namespace.len),
        );
        self.logic.assert_all(
            "namespace_before_digest",
            &[
                arithmetic,
                self.boolean.assert_true(
                    "lt",
                    &self.bv.lt(&text_end, &self.bv.zext::<16, 17>(digest)),
                ),
            ],
        )
    }

    fn shift_preimage(
        &self,
        offset: &HashIndex<L>,
        preimage_length_bytes: &HashIndex<L>,
        shift_base_bits: usize,
        len_bytes: usize,
        preimage: &[V8<L>],
        zz: &V8<L>,
    ) -> (Vec<V8<L>>, L::Assertions) {
        let assertions = self.assert_preimage_range(
            offset,
            preimage_length_bytes,
            &self.bv.of_u64::<K_HASH_INDEX_BITS>(len_bytes as u64),
        );
        let shifted = self
            .routing
            .shift_bitvec(shift_base_bits, offset, len_bytes, preimage, zz);
        (shifted, assertions)
    }

    fn assert_preimage_range(
        &self,
        offset: &HashIndex<L>,
        preimage_length_bytes: &HashIndex<L>,
        consumed: &HashIndex<L>,
    ) -> L::Assertions {
        // Routing can read the entire padded buffer. Authenticate the complete
        // consumed range, not just its start, before accepting those bytes.
        let (end, carry) = self.bv.checked_add(
            &self.bv.zext::<16, 17>(offset),
            &self.bv.zext::<16, 17>(consumed),
        );
        let end_fits = self
            .bv
            .leq(&end, &self.bv.zext::<16, 17>(preimage_length_bytes));
        self.assert_preimage_bounds(offset, preimage_length_bytes, &end_fits, carry)
    }

    fn assert_preimage_bounds(
        &self,
        offset: &HashIndex<L>,
        preimage_length_bytes: &HashIndex<L>,
        end_fits: &crate::circuits::boolean::Bitw<L>,
        arithmetic: L::Assertions,
    ) -> L::Assertions {
        self.logic.assert_all(
            "shift_preimage_bounds",
            &[
                self.boolean.assert_true(
                    "ge_mso",
                    &self.bv.leq(
                        &self.bv.of_u64::<16>((K_COSE1_PREFIX_LEN + 8) as u64),
                        offset,
                    ),
                ),
                self.boolean
                    .assert_true("lt", &self.bv.lt(offset, preimage_length_bytes)),
                arithmetic,
                self.boolean.assert_true("end", end_fits),
            ],
        )
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
