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
    circuits::{
        analog_adder::FieldWrappingSum,
        bitvec::{Bitvec, BitvecLogic, V256, V32, V8},
        boolean::{Bitw, Boolean},
        memcmp::Memcmp,
        routing::Routing,
        sha256msg::{Given as ShaGiven, Sha256Msg},
    },
    compile::logic::Logic,
    mdoc::{
        circuits::cbor_decoder::CborByteDecoder,
        proto::mso_attribute::constants::{
            K_ATTR_COMPARISON_BITS, K_ATTR_ID_BYTES, K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN,
            K_ATTR_VALUE_BYTES, K_DATE_ATTR_PREIMAGE_LEN, K_DATE_ATTR_SHA_BLOCKS,
            K_DATE_VALUE_BYTES, K_DIGEST_ID, K_ELEMENT_IDENTIFIER_PREFIX, K_ELEMENT_VALUE_PREFIX,
            K_MAX_ATTR_SHA_BLOCKS, K_ORDERED_DATE_ENCODINGS, K_RANDOM_ID,
        },
    },
};

pub type AttrIndex<L> = Bitvec<L, K_ATTR_INDEX_BITS>;

#[cfg(test)]
mod tests;

pub type AttrSlice<L, const N: usize> =
    crate::circuits::bitvec::Slice<L, V8<L>, N, K_ATTR_INDEX_BITS>;

/// Public attribute name, operand and enable bit. Only the date slot has
/// comparison flags. Its operand buffer is extended with constant zeros.
pub struct DisclosedAttribute<L: Logic> {
    pub expected_name: AttrSlice<L, K_ATTR_ID_BYTES>,
    pub expected_cbor_value: AttrSlice<L, K_ATTR_VALUE_BYTES>,
    pub enabled: Bitw<L>,
    pub comparison: Option<Bitvec<L, K_ATTR_COMPARISON_BITS>>,
}

impl<L: Logic> Clone for DisclosedAttribute<L> {
    fn clone(&self) -> Self {
        Self {
            expected_name: self.expected_name.clone(),
            expected_cbor_value: self.expected_cbor_value.clone(),
            enabled: self.enabled.clone(),
            comparison: self.comparison.clone(),
        }
    }
}

/// Represents the offset and length (slice parameters) of an attribute field
/// inside the CBOR block.
pub struct Slice<L: Logic> {
    /// Offset of the field (in bytes) relative to the start of the outer
    /// tagged CBOR byte array.
    pub offset: AttrIndex<L>,
    /// Length of the field (in bytes).
    pub len: AttrIndex<L>,
}

impl<L: Logic> Clone for Slice<L> {
    fn clone(&self) -> Self {
        Self {
            offset: self.offset.clone(),
            len: self.len.clone(),
        }
    }
}

/// Represents the CBOR list structure of `IssuerSignedItem` (the field
/// locator). Contains start indices and lengths of the 4 fields (digestID,
/// random salt, elementIdentifier, elementValue), along with permutation
/// controls to handle any arbitrary field ordering.
pub struct FieldLocator<L: Logic> {
    /// Start indices of each of the 4 fields in the CBOR map.
    pub slot_position: [AttrIndex<L>; 4],
    /// Lengths of each of the 4 fields in the list.
    pub length: [AttrIndex<L>; 4],
    /// Permutation mapping from logical slots to physical field indices [0..3]
    /// in the CBOR map. Specifically:
    /// - `permutation[0]` selects the physical index containing "digestID" (logical slot 0).
    /// - `permutation[1]` selects the physical index containing "random" salt (logical slot 1).
    /// - `permutation[2]` selects the physical index containing "elementIdentifier" (logical slot
    ///   2).
    /// - `permutation[3]` selects the physical index containing "elementValue" (logical slot 3).
    pub permutation: [Bitvec<L, 2>; 4],
}

impl<L: Logic> Clone for FieldLocator<L> {
    fn clone(&self) -> Self {
        Self {
            slot_position: self.slot_position.clone(),
            length: self.length.clone(),
            permutation: self.permutation.clone(),
        }
    }
}

pub struct Given<L: crate::compile::logic::Logic> {
    pub attribute_preimage: AttrSlice<L, K_ATTR_PREIMAGE_LEN>,
    pub field_locator: FieldLocator<L>,
    pub disclosed_attribute: DisclosedAttribute<L>,
    pub expected_digest: V256<L>,
}

pub type Derived<L> = crate::circuits::sha256msg::Derived<V32<L>>;

pub struct AttributeVerifier<'a, L: Logic>
where L::F: FieldWrappingSum
{
    logic: &'a L,
    boolean: Boolean<'a, L>,
    bv: BitvecLogic<'a, L>,
    cbor_decoder: CborByteDecoder<'a, L>,
    routing: Routing<'a, L>,
}

impl<'a, L: Logic> AttributeVerifier<'a, L>
where L::F: FieldWrappingSum
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            boolean: Boolean::new(logic),
            bv: BitvecLogic::new(logic),
            cbor_decoder: CborByteDecoder::new(logic),
            routing: Routing::new(logic),
        }
    }

    pub fn assert_attribute(&self, given: &Given<L>, derived: &Derived<L>) -> L::Assertions {
        let attribute = &given.disclosed_attribute;
        let preimage = &given.attribute_preimage;
        let bytes = if attribute.comparison.is_some() {
            &preimage.data[..K_DATE_ATTR_PREIMAGE_LEN]
        } else {
            &preimage.data
        };
        let value = match &attribute.comparison {
            Some(comparison) => self.assert_date_value(
                &given.field_locator,
                bytes,
                &attribute.expected_cbor_value,
                comparison,
            ),
            None => self.assert_item_slot_key_value(
                3,
                &given.field_locator,
                bytes,
                K_ELEMENT_VALUE_PREFIX.len() + 1 + K_ATTR_VALUE_BYTES,
                &K_ELEMENT_VALUE_PREFIX,
                &attribute.expected_cbor_value,
            ),
        };
        let enabled = self.boolean.as_eltw(&attribute.enabled);
        let slot_checks = [
            self.assert_preimage_header(&given.attribute_preimage),
            self.assert_segments(&given.field_locator, &given.attribute_preimage.len),
            self.assert_permutation(&given.field_locator.permutation),
            self.assert_item_slot_key_only(0, &given.field_locator, bytes, &K_DIGEST_ID, true),
            self.assert_item_slot_key_only(1, &given.field_locator, bytes, &K_RANDOM_ID, false),
            self.assert_item_slot_key_value(
                2,
                &given.field_locator,
                bytes,
                K_ELEMENT_IDENTIFIER_PREFIX.len() + 1 + K_ATTR_ID_BYTES,
                &K_ELEMENT_IDENTIFIER_PREFIX,
                &given.disclosed_attribute.expected_name,
            ),
            value,
            self.assert_sha_digest(bytes, given, derived),
        ];
        let mut checks: Vec<_> = slot_checks
            .into_iter()
            .map(|check| self.logic.assert_when(&enabled, check))
            .collect();
        checks.push(self.assert_disabled_inputs(attribute));
        self.logic.assert_all("assert_attribute", &checks)
    }

    fn assert_disabled_inputs(&self, attribute: &DisclosedAttribute<L>) -> L::Assertions {
        let assert_zero_bytes = |name, data: &[V8<L>]| {
            self.logic
                .assert_mapi(name, 0..data.len().div_ceil(8), |i| {
                    let chunk = &data[8 * i..(8 * (i + 1)).min(data.len())];
                    let bits = self.bv.from_fn::<64, _>(|k| {
                        chunk
                            .get(k / 8)
                            .map_or_else(|| self.boolean.falseb(), |byte| byte.bit(k % 8).clone())
                    });
                    self.bv.assert_eq("zero", &bits, &self.bv.zero())
                })
        };
        let disabled = self.boolean.as_eltw(&self.boolean.notb(&attribute.enabled));
        let size = if attribute.comparison.is_some() {
            K_DATE_VALUE_BYTES
        } else {
            K_ATTR_VALUE_BYTES
        };
        let comparison = attribute.comparison.as_ref().map_or_else(
            || self.logic.ok(),
            |op| self.bv.assert_eq("comparison", op, &self.bv.zero()),
        );
        let zero = self.logic.assert_all(
            "disabled_inputs",
            &[
                assert_zero_bytes("name", &attribute.expected_name.data),
                self.bv
                    .assert_eq("name_length", &attribute.expected_name.len, &self.bv.zero()),
                assert_zero_bytes("value", &attribute.expected_cbor_value.data[..size]),
                self.bv.assert_eq(
                    "value_length",
                    &attribute.expected_cbor_value.len,
                    &self.bv.zero(),
                ),
                comparison,
            ],
        );
        self.logic.assert_when(&disabled, zero)
    }

    fn assert_sha_digest(
        &self,
        preimage: &[V8<L>],
        given: &Given<L>,
        derived: &Derived<L>,
    ) -> L::Assertions {
        let len = &given.attribute_preimage.len;
        let length_bytes = self.bv.zext(len);
        if given.disclosed_attribute.comparison.is_some() {
            let date = ShaGiven {
                padded_preimage: preimage.to_vec(),
                nblocks: self.bv.of_u64::<2>(K_DATE_ATTR_SHA_BLOCKS as u64),
                length_bytes,
                expected_hash: given.expected_digest.clone(),
            };
            return Sha256Msg::<_, K_DATE_ATTR_SHA_BLOCKS>::new(self.logic)
                .assert_message_hash(&date, derived);
        }
        // ceil((len + 9) / 64) = (len + 72) >> 6. The SHA gadget checks
        // the count against the full length and the four-block capacity.
        let (padded_len, no_overflow) = self.bv.checked_add(len, &self.bv.of_u64(72));
        let ordinary = ShaGiven {
            padded_preimage: preimage.to_vec(),
            nblocks: self.bv.from_fn::<3, _>(|i| padded_len.bit(6 + i).clone()),
            length_bytes,
            expected_hash: given.expected_digest.clone(),
        };
        self.logic.assert_all(
            "attribute_digest",
            &[
                no_overflow,
                Sha256Msg::<_, K_MAX_ATTR_SHA_BLOCKS>::new(self.logic)
                    .assert_message_hash(&ordinary, derived),
            ],
        )
    }

    fn assert_preimage_header(
        &self,
        attribute_preimage: &AttrSlice<L, K_ATTR_PREIMAGE_LEN>,
    ) -> L::Assertions {
        // Verify the cbor prefix for IssuerSignedItem.
        // attribute_preimage.data[0..3] is [0xD8, 0x18, 0x58] (Tag 24, and
        // Byte String header). attribute_preimage.data[3] contains the
        // payload length, which varies and is privately constrained
        // to be equal to `attribute_preimage.len` (checked below by the sum of
        // map item sizes). attribute_preimage.data[4] is [0xA4] (the
        // map size of 4).
        let cbor_tag = [0xD8, 0x18, 0x58];
        let cbor_array = [0xA4];

        // Constrain the length byte in the CBOR byte string header to match the
        // expected payload length
        let preimage_len_16 = self
            .bv
            .zext::<8, K_ATTR_INDEX_BITS>(&attribute_preimage.data[3]);
        let four = self.bv.of_u64::<K_ATTR_INDEX_BITS>(4);

        self.logic.assert_all(
            "assert_preimage_header",
            &[
                self.assert_bytes_at(3, &attribute_preimage.data[0..3], &cbor_tag),
                self.assert_bytes_at(1, &attribute_preimage.data[4..5], &cbor_array),
                self.bv
                    .assert_checked_add(&attribute_preimage.len, &preimage_len_16, &four),
            ],
        )
    }

    fn assert_bytes_at(&self, len: usize, buf: &[V8<L>], want: &[u8]) -> L::Assertions {
        self.logic.assert_mapi("assert_bytes_at", 0..len, |i| {
            self.bv
                .assert_eq("bytes_at", &buf[i], &self.bv.of_u8(want[i]))
        })
    }

    /// Asserts that all layout segments within the `FieldLocator` map are
    /// contiguous and valid. Specifically:
    /// - Checks that the first physical segment starts at byte index 5.
    /// - Verifies that each subsequent segment starts immediately after the previous one.
    /// - Verifies that the final segment ends precisely at the expected payload length.
    fn assert_segments(
        &self,
        field_locator: &FieldLocator<L>,
        expected_payload_len: &AttrIndex<L>,
    ) -> L::Assertions {
        let five = self.bv.of_u64::<K_ATTR_INDEX_BITS>(5);

        let first_segment = self.bv.assert_eq(
            "first_segment_start",
            &field_locator.slot_position[0],
            &five,
        );

        let contiguous_segments = self.logic.assert_mapi("contiguous_segments", 0..3, |j| {
            self.bv.assert_checked_add(
                &field_locator.slot_position[j + 1],
                &field_locator.slot_position[j],
                &field_locator.length[j],
            )
        });

        let payload_len = self.bv.assert_checked_add(
            expected_payload_len,
            &field_locator.slot_position[3],
            &field_locator.length[3],
        );

        self.logic.assert_all(
            "assert_segments",
            &[first_segment, contiguous_segments, payload_len],
        )
    }

    /// Asserts that the permutation mapping is a bijection (all physical index
    /// selections are unique).
    ///
    /// # Note on Redundancy
    /// This check is technically redundant for security because the four
    /// logical slots are verified against four distinct, mutually exclusive
    /// constant key prefixes:
    /// - `"digestID"`
    /// - `"random"`
    /// - `"elementIdentifier"`
    /// - `"elementValue"`
    ///
    /// Since no single physical item in the CBOR buffer can satisfy more than
    /// one of these prefixes, the slot prefix checks already implicitly
    /// enforce that the selected physical items must be distinct.
    ///
    /// We keep this check anyway for:
    /// 1. **Defense-in-depth**: It prevents vulnerabilities if the prefix checks or key names are
    ///    ever modified, weakened, or bypassed in future updates.
    /// 2. **Auditability**: It makes circuit correctness obvious to reviewers by explicitly
    ///    enforcing the uniqueness property of the permutation mapping at the gate level.
    fn assert_permutation(&self, permutation: &[Bitvec<L, 2>; 4]) -> L::Assertions {
        const PAIRS: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
        self.logic.assert_mapi("assert_permutation", 0..6, |k| {
            let (i, j) = PAIRS[k];
            self.bv
                .assert_neq("perm_neq", &permutation[i], &permutation[j])
        })
    }

    fn assert_item_slot_key_value<const N: usize>(
        &self,
        slot: usize,
        field_locator: &FieldLocator<L>,
        attribute_preimage: &[V8<L>],
        max_len: usize,
        prefix: &[u8],
        str_val: &AttrSlice<L, N>,
    ) -> L::Assertions {
        let want = self.format_element(max_len, prefix, &str_val.data);
        let slice = self.slot_offset_and_len(slot, field_locator);
        let got = self.routing.shift_bitvec(
            3,
            &slice.offset,
            max_len,
            attribute_preimage,
            &self.bv.zero::<8>(),
        );
        let prefix_len = self.bv.of_u64::<K_ATTR_INDEX_BITS>(prefix.len() as u64);
        let (expected_slice_len, overflow_assertion) =
            self.bv.checked_add(&prefix_len, &str_val.len);

        self.logic.assert_all(
            "assert_item_slot_key_value",
            &[
                overflow_assertion,
                self.boolean.assert_true(
                    "public_length",
                    &self
                        .bv
                        .leq(&str_val.len, &self.bv.of_u64::<K_ATTR_INDEX_BITS>(N as u64)),
                ),
                self.assert_prefix_equal(max_len, &got, &want, &expected_slice_len),
                self.assert_len_eq(&slice.len, &expected_slice_len),
            ],
        )
    }

    fn assert_date_value(
        &self,
        field_locator: &FieldLocator<L>,
        attribute_preimage: &[V8<L>],
        want: &AttrSlice<L, K_ATTR_VALUE_BYTES>,
        comparison: &Bitvec<L, K_ATTR_COMPARISON_BITS>,
    ) -> L::Assertions {
        let slice = self.slot_offset_and_len(3, field_locator);
        let key_bytes = K_ELEMENT_VALUE_PREFIX.len();
        let aligned = self.routing.shift_bitvec(
            3,
            &slice.offset,
            key_bytes + K_DATE_VALUE_BYTES,
            attribute_preimage,
            &self.bv.zero::<8>(),
        );
        let (key, got) = aligned.split_at(key_bytes);
        let key_len = self.bv.of_u64::<K_ATTR_INDEX_BITS>(key.len() as u64);
        let (expected_slice_len, overflow) = self.bv.checked_add(&key_len, &want.len);

        let le = comparison.bit(0);
        let ge = comparison.bit(1);
        let ordered = self.boolean.orb(le, ge);
        let valid_op = self
            .boolean
            .assert_false("valid_op", &self.boolean.andb(le, ge));
        let date_format = K_ORDERED_DATE_ENCODINGS.iter().fold(
            self.boolean.falseb(),
            |matches_format, &(header, len)| {
                let length = self.bv.of_u64::<K_ATTR_INDEX_BITS>(len as u64);
                let same_len = self.bv.eqb(&want.len, &length);
                let same_header = got.iter().zip(&want.data).zip(header).fold(
                    same_len,
                    |matches_header, ((actual, expected), &byte)| {
                        let header_byte = self.bv.of_u8(byte);
                        self.boolean.andb(
                            &matches_header,
                            &self.boolean.andb(
                                &self.bv.eqb(actual, &header_byte),
                                &self.bv.eqb(expected, &header_byte),
                            ),
                        )
                    },
                );
                self.boolean.orb(&matches_format, &same_header)
            },
        );

        let in_range = |i| self.bv.lt(&self.bv.of_u64(i as u64), &want.len);
        let right = &want.data[..K_DATE_VALUE_BYTES];
        let left: Vec<_> = (0..K_DATE_VALUE_BYTES)
            .map(|i| self.bv.select(&in_range(i), &got[i], &right[i]))
            .collect();
        let (lt, eq) = Memcmp::new(self.logic).lt_eq(&left, right);
        // Eq wants eq; Le accepts eq or lt; Ge accepts eq or gt.
        let ordered_match = self.boolean.andb(&ordered, &self.boolean.xorb(&lt, ge));
        let relation = self.boolean.orb(&eq, &ordered_match);

        self.logic.assert_all(
            "assert_date_value",
            &[
                self.assert_bytes_at(key.len(), key, &K_ELEMENT_VALUE_PREFIX),
                overflow,
                self.assert_len_eq(&slice.len, &expected_slice_len),
                valid_op,
                self.boolean.assert_true("date_format", &date_format),
                self.boolean.assert_true("relation", &relation),
            ],
        )
    }

    /// Verifies the structural integrity and prefix key matching for a private
    /// layout slot. Specifically:
    /// - Multiplexes the start index (shift) and length of the physical slot mapping.
    /// - Shifts the preimage block to align the slot start at index 0.
    /// - Asserts that the slot starts exactly with the expected key prefix (`key_id`).
    /// - Decodes the CBOR header prefix and asserts that the header length plus actual content
    ///   length matches the multiplexed segment length.
    fn assert_item_slot_key_only(
        &self,
        slot: usize,
        field_locator: &FieldLocator<L>,
        attribute_preimage: &[V8<L>],
        key_id: &[u8],
        is_unsigned: bool,
    ) -> L::Assertions {
        let zz = self.bv.zero::<8>();
        let slice = self.slot_offset_and_len(slot, field_locator);
        let got =
            self.routing
                .shift_bitvec(3, &slice.offset, key_id.len() + 2, attribute_preimage, &zz);
        self.logic.assert_all(
            "assert_item_slot_key_only",
            &[
                self.assert_bytes_at(key_id.len(), &got[0..key_id.len()], key_id),
                // The general CBOR helper classifies lengths for many types;
                // these two schema slots require unsigned IDs and byte salts.
                self.boolean.assert_true(
                    "major_type",
                    &self.bv.eqmask(
                        &got[key_id.len()],
                        if is_unsigned { 0x00 } else { 0x40 },
                        0xe0,
                    ),
                ),
                self.assert_cbor_length(&got, &slice.len, key_id.len(), is_unsigned),
            ],
        )
    }

    /// Parses the CBOR header at `val_hdr_index` of `buf` and asserts that the
    /// header length plus the actual content length is equal to the
    /// expected total length (`expected_len`).
    ///
    /// If `atom` is true, parses an atomic CBOR element (e.g. tag, integer, or
    /// tiny text). If false, handles structured values that could span
    /// multiple bytes for their length field.
    fn assert_cbor_length(
        &self,
        attribute_preimage: &[V8<L>],
        expected_len: &AttrIndex<L>,
        val_hdr_index: usize,
        atom: bool,
    ) -> L::Assertions {
        let (cbor, cbor_assert) = self
            .cbor_decoder
            .decode_one_v8::<K_ATTR_INDEX_BITS>(&attribute_preimage[val_hdr_index]);

        let length_from_next_byte = self
            .bv
            .zext::<8, K_ATTR_INDEX_BITS>(&attribute_preimage[val_hdr_index + 1]);
        let content_len = self.bv.select(
            &cbor.length_plus_next_v8,
            &length_from_next_byte,
            &self.bv.zero::<K_ATTR_INDEX_BITS>(),
        );
        let (v_len, add_assert) = self.bv.checked_add(&cbor.length, &content_len);
        let k_len = self.bv.of_u64::<K_ATTR_INDEX_BITS>(val_hdr_index as u64);
        let checked_add_assert = self.bv.assert_checked_add(expected_len, &k_len, &v_len);

        let count27_assert = if atom {
            self.boolean.assert_false("count27", &cbor.count27)
        } else {
            self.boolean.assert_true("trueb", &self.boolean.trueb())
        };

        let assertions = vec![
            cbor_assert,
            self.boolean.assert_false("invalid", &cbor.invalid),
            add_assert,
            checked_add_assert,
            count27_assert,
        ];

        self.logic.assert_all("assert_cbor_length", &assertions)
    }

    /// Formats a CBOR map element by prepending the CBOR header prefix (e.g.
    /// key length tag and key name string bytes) to the element value
    /// bytes, and zero-padding the resulting buffer up to a fixed maximum
    /// length `max`.
    fn format_element(&self, max: usize, prefix: &[u8], str_val: &[V8<L>]) -> Vec<V8<L>> {
        assert!(prefix.len() + str_val.len() <= max);
        let zero = self.bv.of_u8(0);
        prefix
            .iter()
            .map(|&x| self.bv.of_u8(x))
            .chain(str_val.iter().cloned())
            .chain(std::iter::repeat(zero))
            .take(max)
            .collect()
    }

    pub fn slot_offset_and_len(&self, slot: usize, field_locator: &FieldLocator<L>) -> Slice<L> {
        let zero = self.bv.of_u64::<K_ATTR_INDEX_BITS>(0);
        let offset = self.routing.shift_bitvec(
            1,
            &field_locator.permutation[slot],
            1,
            &field_locator.slot_position,
            &zero,
        )[0]
        .clone();
        let len = self.routing.shift_bitvec(
            1,
            &field_locator.permutation[slot],
            1,
            &field_locator.length,
            &zero,
        )[0]
        .clone();
        Slice { offset, len }
    }

    pub fn assert_prefix_equal(
        &self,
        max: usize,
        got: &[V8<L>],
        want: &[V8<L>],
        len: &AttrIndex<L>,
    ) -> L::Assertions {
        self.logic.assert_mapi("assert_prefix_equal", 0..max, |j| {
            let j_wire = self.bv.of_u64::<K_ATTR_INDEX_BITS>(j as u64);
            let ll = self.bv.lt(&j_wire, len);
            let ll_vec = self.bv.of_bit::<8>(&ll);
            let eqb_vec = self.bv.eq(&got[j], &want[j]);
            let imp_vec = self.bv.impliesb(&ll_vec, &eqb_vec);
            self.bv.assert_true("prefix_imp", &imp_vec)
        })
    }

    fn assert_len_eq(&self, cbor_len: &AttrIndex<L>, pub_len: &AttrIndex<L>) -> L::Assertions {
        self.bv.assert_eq("cbor_len_eq", cbor_len, pub_len)
    }
}
