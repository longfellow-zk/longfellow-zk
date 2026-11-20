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

use super::shape::Derived;
use crate::{
    circuits::{
        analog_adder::AnalogAdder,
        arithmetic::Arithmetic,
        bitvec::{Bitvec, BitvecLogic, V256, V32, V8},
        boolean::{Bitw, Boolean},
        memcmp::Memcmp,
        routing::Routing,
        sha256msg::{pack_digest, Sha256Msg},
    },
    compile::logic::{Eltw, Logic, LogicIO},
    mdoc::{
        circuits::{
            mso_attribute::{AttrSlice, AttributeVerifier, FieldLocator, PackedRead},
            MdocHashCompileField,
        },
        proto::{
            hash::constants::{
                K_COSE1_PREFIX, K_COSE1_PREFIX_LEN, K_DEVICE_KEY_INFO_CHECK_CBOR,
                K_DOCTYPE_HEADER_CHECK_CBOR, K_DOC_TYPE_BYTES, K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS,
                K_MSO_OFFSET, K_MSO_PREIMAGE_LEN, K_NAMESPACE_BYTES, K_TAG32,
                K_VALID_FROM_CHECK_CBOR, K_VALID_UNTIL_CHECK_CBOR, K_VALUE_DIGESTS_CHECK_CBOR,
            },
            mso_attribute::constants::{K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN},
        },
    },
};

pub(super) type HashIndex<L> = Bitvec<L, K_HASH_INDEX_BITS>;

const MSO_SHIFT_GROUPS: [usize; 4] = [4, 3, 3, 2];

#[derive(Clone)]
pub struct HashBytes<L: Logic, const N: usize> {
    pub value: [V8<L>; N],
    pub len: HashIndex<L>,
}

#[cfg(test)]
mod tests;

pub(super) type AttrPreimageBytes<L> = AttrSlice<L, K_ATTR_PREIMAGE_LEN>;
pub(super) type MsoPreimageBytes<L> = HashBytes<L, K_MSO_PREIMAGE_LEN>;

pub struct AttrGiven<L: Logic> {
    pub preimage: AttrPreimageBytes<L>,
    pub mso_digest_offset_in_preimage: HashIndex<L>,
    pub field_locator: FieldLocator<L>,
}

use crate::mdoc::{
    circuits::mso_attribute::DisclosedAttribute,
    proto::hash::constants::{K_TIMESTAMP_DIGITS, K_TIMESTAMP_LEN},
};

pub struct Given<L: LogicIO> {
    pub disclosed_attributes: Vec<DisclosedAttribute<L>>,
    pub now: [V8<L>; K_TIMESTAMP_DIGITS.len()],
    pub suppress_doc_type_check: Bitw<L>,
    pub expected_doc_type: AttrSlice<L, K_DOC_TYPE_BYTES>,
    pub expected_namespace: AttrSlice<L, K_NAMESPACE_BYTES>,
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

pub struct MdocHash<'a, L: LogicIO>
where L::F: MdocHashCompileField
{
    pub(in crate::mdoc::circuits) logic: &'a L,
    pub(in crate::mdoc::circuits) shamsg_mso: Sha256Msg<'a, L, K_MAX_SHA_BLOCKS>,
    pub(in crate::mdoc::circuits) routing: Routing<'a, L>,
    pub(in crate::mdoc::circuits) boolean: Boolean<'a, L>,
    pub(in crate::mdoc::circuits) bv: BitvecLogic<'a, L>,
    pub(in crate::mdoc::circuits) arith: Arithmetic<'a, L>,
    pub(in crate::mdoc::circuits) cmp_helper: Memcmp<'a, L>,
    pub(in crate::mdoc::circuits) attribute_verifier: AttributeVerifier<'a, L>,
}

impl<'a, L: LogicIO> MdocHash<'a, L>
where L::F: MdocHashCompileField
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            shamsg_mso: Sha256Msg::new(logic),
            routing: Routing::new(logic),
            boolean: Boolean::new(logic),
            bv: BitvecLogic::new(logic),
            arith: Arithmetic::new(logic),
            cmp_helper: Memcmp::new(logic),
            attribute_verifier: AttributeVerifier::new(logic),
        }
    }

    pub fn assert_valid_presentation(
        &self,
        given: &Given<L>,
        derived: &Derived<V32<L>>,
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
        derived: &Derived<V32<L>>,
        preimage: &[V8<L>],
    ) -> L::Assertions {
        let preimage_len_64 = self
            .bv
            .zext::<{ K_HASH_INDEX_BITS }, 64>(&given.preimage.len);
        let nblocks_ext = self.bv.zext::<8, { K_MAX_SHA_BLOCKS }>(&given.nblocks);

        let shamsg_given = crate::circuits::sha256msg::Given {
            padded_preimage: preimage.to_vec(),
            nblocks: nblocks_ext,
            length_bytes: preimage_len_64,
            expected_hash: pack_digest(self.logic, &given.issuer_sig_e),
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
        expected: &AttrSlice<L, N>,
        enabled: &Bitw<L>,
        prefix: &[u8],
        preimage: &[V8<L>],
    ) -> [L::Assertions; 5] {
        // Lookahead covers both supported text headers. Only the bytes consumed
        // by the selected header and value must be inside the signed message.
        let read = PackedRead::new(
            self.logic,
            &MSO_SHIFT_GROUPS,
            offset,
            prefix.len() + N + 2,
            preimage,
            1,
        );
        let w = read.w();
        let header_check = self.arith.assert_units_eq_when(
            "cbor_header",
            enabled,
            read.units(0..prefix.len()),
            &read.const_units(prefix),
            w,
        );

        let head_byte = &read.bits(prefix.len());
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
                .zext::<8, K_ATTR_INDEX_BITS>(&read.bits(prefix.len() + 1)),
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

            let start = prefix.len() + 1 + i;
            let two = self.boolean.as_eltw(&is_two_byte_header);
            let got: Vec<_> = read
                .units(start..start + 1)
                .iter()
                .zip(read.units(start + 1..start + 2))
                .map(|(if_1, if_2)| {
                    self.logic
                        .add(if_1, &self.logic.mul(&two, &self.logic.sub(if_2, if_1)))
                })
                .collect();
            let want = read.byte_units(std::slice::from_ref(&expected.data[i]));
            self.arith
                .assert_units_eq_when("text_byte", &active, &got, &want, w)
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
        let adder = AnalogAdder::new(self.logic);
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
                self.bv.of_u64::<17>(K_MSO_OFFSET as u64),
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
                    &self.bv.eqmask(&preimage[K_MSO_OFFSET], 0xa0, 0xe0),
                ),
            ],
        )
    }

    fn assert_mso_validity(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        // Well-formed 20-byte UTC dates sort by their digits. Separators have
        // no ordering meaning, and RFC 3339 permits both T/t and Z/z.
        let check = |name: &str, offset: &HashIndex<L>, key: &[u8], before: bool| {
            let len = key.len() + K_TIMESTAMP_LEN;
            let range = self.assert_preimage_range(
                offset,
                &given.preimage.len,
                &self.bv.of_u64::<K_HASH_INDEX_BITS>(len as u64),
            );
            let read = PackedRead::new(self.logic, &MSO_SHIFT_GROUPS, offset, len, preimage, 1);
            let digits = K_TIMESTAMP_DIGITS.map(|i| read.bits(key.len() + i));
            let ordered = if before {
                self.cmp_helper.leq(&digits, &given.now)
            } else {
                self.cmp_helper.leq(&given.now, &digits)
            };
            self.logic.assert_all(
                name,
                &[
                    range,
                    read.assert_bytes_at("assert_bytes_at", 0, key),
                    self.boolean
                        .assert_true(if before { "cmp_from" } else { "cmp_until" }, &ordered),
                ],
            )
        };
        self.logic.assert_all(
            "assert_mso_validity",
            &[
                check(
                    "valid_from",
                    &given.valid_from_offset_in_preimage,
                    &K_VALID_FROM_CHECK_CBOR,
                    true,
                ),
                check(
                    "valid_until",
                    &given.valid_until_offset_in_preimage,
                    &K_VALID_UNTIL_CHECK_CBOR,
                    false,
                ),
            ],
        )
    }

    fn assert_mso_device_key(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let info = K_DEVICE_KEY_INFO_CHECK_CBOR.len();
        let (shifted, shift_assertions) = self.shift_preimage_packed(
            &given.dev_key_info_offset_in_preimage,
            &given.preimage.len,
            info + 32 + 3 + 32,
            preimage,
        );
        let dpky_check = [0x22, 0x58, 0x20];

        self.logic.assert_all(
            "assert_mso_device_key",
            &[
                shift_assertions,
                self.assert_packed_at(&shifted[0..info], &K_DEVICE_KEY_INFO_CHECK_CBOR),
                self.assert_key(&given.device_pk.0, &shifted[info..info + 32]),
                self.assert_packed_at(&shifted[info + 32..info + 35], &dpky_check),
                self.assert_key(&given.device_pk.1, &shifted[info + 35..info + 67]),
            ],
        )
    }

    fn assert_mso_value_digests(&self, given: &Given<L>, preimage: &[V8<L>]) -> L::Assertions {
        let (shifted, shift_assertions) = self.shift_preimage_packed(
            &given.value_digests_offset_in_preimage,
            &given.preimage.len,
            K_VALUE_DIGESTS_CHECK_CBOR.len(),
            preimage,
        );
        self.logic.assert_all(
            "assert_mso_value_digests",
            &[
                shift_assertions,
                self.assert_packed_at(&shifted, &K_VALUE_DIGESTS_CHECK_CBOR),
            ],
        )
    }

    fn assert_attributes(
        &self,
        given: &Given<L>,
        derived: &Derived<V32<L>>,
        preimage: &[V8<L>],
    ) -> L::Assertions {
        self.logic.assert_mapi(
            "assert_attributes",
            0..given.disclosed_attributes.len(),
            |i| {
                let attr_given = &given.attribute_given[i];
                let attr_der = &derived.attribute_derived[i];
                let disclosed = &given.disclosed_attributes[i];
                let enabled = self.boolean.as_eltw(&disclosed.enabled);

                let (mso_digest_shifted, shift_assertions) = self.shift_preimage_packed(
                    &attr_given.mso_digest_offset_in_preimage,
                    &given.preimage.len,
                    K_TAG32.len() + 32,
                    preimage,
                );
                let (tag, digest) = mso_digest_shifted.split_at(K_TAG32.len());
                let expected_digest = std::array::from_fn(|byte| digest[byte].clone());
                let tag32_header_assertion = self.assert_packed_at(tag, &K_TAG32);

                let verifier_given = crate::mdoc::circuits::mso_attribute::Given {
                    attribute_preimage: attr_given.preimage.clone(),
                    field_locator: attr_given.field_locator.clone(),
                    disclosed_attribute: disclosed.clone(),
                    expected_digest,
                };
                let attribute_verifier_assertions = self
                    .attribute_verifier
                    .assert_attribute(&verifier_given, &attr_der.sha_derived);

                self.logic.assert_all(
                    "attribute_item",
                    &[
                        self.logic.assert_when(&enabled, shift_assertions),
                        self.logic.assert_when(&enabled, tag32_header_assertion),
                        self.logic.assert_when(
                            &enabled,
                            self.assert_namespace_before_digest(
                                given,
                                &attr_given.mso_digest_offset_in_preimage,
                            ),
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

    /// Read a field that is only compared: the bytes are shifted as packed
    /// field elements, one term per byte and selector, after checking that
    /// the whole field lies inside the signed message.
    fn shift_preimage_packed(
        &self,
        offset: &HashIndex<L>,
        preimage_length_bytes: &HashIndex<L>,
        len_bytes: usize,
        preimage: &[V8<L>],
    ) -> (Vec<Eltw<L>>, L::Assertions) {
        let assertions = self.assert_preimage_range(
            offset,
            preimage_length_bytes,
            &self.bv.of_u64::<K_HASH_INDEX_BITS>(len_bytes as u64),
        );
        let packed: Vec<_> = preimage
            .iter()
            .map(|byte| self.arith.pack_byte(byte.as_array()))
            .collect();
        let shifted =
            self.routing
                .shift_eltw_grouped(&MSO_SHIFT_GROUPS, offset, len_bytes, &packed);
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
        end_fits: &Bitw<L>,
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

    fn assert_key(&self, key: &V256<L>, buf_be: &[Eltw<L>]) -> L::Assertions {
        let bytes_le: Vec<_> = buf_be.iter().rev().cloned().collect();
        self.arith
            .assert_eq_packed_bytes("key_eq", key.as_array(), &bytes_le)
    }

    fn assert_packed_at(&self, buf: &[Eltw<L>], want: &[u8]) -> L::Assertions {
        let packed: Vec<_> = want
            .iter()
            .map(|&byte| self.arith.pack_byte(self.bv.of_u8(byte).as_array()))
            .collect();
        self.arith
            .assert_packed_bytes_eq("assert_bytes_at", buf, &packed)
    }
}
