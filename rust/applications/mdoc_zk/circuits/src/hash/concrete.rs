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

use super::constants::K_MSO_PREIMAGE_LEN;
use crate::{
    core::algebra::Nat, mdoc::circuits::mso_attribute::concrete::FieldLocator as MsoFieldLocator,
};

#[derive(Clone, Debug)]
pub struct AttrInput {
    pub expected_name: Vec<u8>,
    pub expected_cbor_value: Vec<u8>,
    pub cbor_issuer_signed_item: Vec<u8>,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
}

#[derive(Clone, Debug)]
pub struct HashInput<N> {
    pub attrs: Vec<AttrInput>,
    pub now: Vec<u8>,
    pub suppress_doc_type_check: bool,
    pub expected_doc_type: Vec<u8>,
    pub cbor_mso: Vec<u8>,
    pub issuer_sig_e: N,
    pub device_pk: (N, N),
    pub doc_type_offset: usize,
    pub valid_from_offset: usize,
    pub valid_until_offset: usize,
    pub dev_key_info_offset: usize,
    pub value_digests_offset: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct HashBytes<const N: usize> {
    pub value: [u8; N],
    pub len: u16,
}

pub type MsoPreimageBytes = HashBytes<K_MSO_PREIMAGE_LEN>;

#[derive(Clone, Debug)]
pub struct AttrGiven {
    pub expected_name: Vec<u8>,
    pub expected_cbor_value: Vec<u8>,
    pub padded_preimage: Vec<u8>,
    pub unpadded_preimage_len: usize,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
}

#[derive(Clone, Debug)]
pub struct AttrDerived {
    pub sha_derived: crate::circuits::sha256msg::concrete::ConcreteDerived,
}

#[derive(Clone, Debug)]
pub struct ConcreteGiven<N> {
    pub hash_input: HashInput<N>,
    pub preimage: MsoPreimageBytes,
    pub nblocks: u8,
    pub doc_type_offset_in_preimage: u16,
    pub valid_from_offset_in_preimage: u16,
    pub valid_until_offset_in_preimage: u16,
    pub dev_key_info_offset_in_preimage: u16,
    pub value_digests_offset_in_preimage: u16,
    pub attribute_given: Vec<AttrGiven>,
}

#[derive(Clone, Debug)]
pub struct ConcreteDerived {
    pub attribute_derived: Vec<AttrDerived>,
    pub sha_derived: crate::circuits::sha256msg::concrete::ConcreteDerived,
}

pub fn given<const W: usize, N: Nat<W>>(hash_input: HashInput<N>) -> ConcreteGiven<N> {
    let cose_sha_wit = crate::circuits::sha256msg::concrete::given(
        &hash_input.cbor_mso,
        &crate::circuits::sha256::constants::INITIAL,
        super::constants::K_MAX_SHA_BLOCKS,
    )
    .unwrap();
    let signed_bytes = cose_sha_wit.padded_preimage;
    let nblocks = cose_sha_wit.nblocks;

    // These raw compiler/test helpers retain their existing panic contract for
    // invalid inputs, but must never silently narrow or wrap an input offset.
    let preimage_base_offset = super::constants::K_COSE1_PREFIX_LEN + 7;
    let offset = |relative: usize| {
        u16::try_from(
            relative
                .checked_add(preimage_base_offset)
                .expect("MSO offset overflow"),
        )
        .expect("MSO offset exceeds its wire width")
    };

    let mut attribute_given = Vec::with_capacity(hash_input.attrs.len());
    for a in &hash_input.attrs {
        let attr_sha_wit = crate::circuits::sha256msg::concrete::given(
            &a.cbor_issuer_signed_item,
            &crate::circuits::sha256::constants::INITIAL,
            2,
        )
        .unwrap();
        attribute_given.push(AttrGiven {
            expected_name: a.expected_name.clone(),
            expected_cbor_value: a.expected_cbor_value.clone(),
            padded_preimage: attr_sha_wit.padded_preimage,
            unpadded_preimage_len: a.cbor_issuer_signed_item.len(),
            mso_digest_offset_in_preimage: usize::from(offset(a.mso_digest_offset_in_preimage)),
            field_locator: a.field_locator,
        });
    }

    let preimage = MsoPreimageBytes {
        value: signed_bytes
            .try_into()
            .expect("MSO padding capacity mismatch"),
        len: u16::try_from(hash_input.cbor_mso.len()).expect("MSO length exceeds its wire width"),
    };

    let doc_type_offset_in_preimage = offset(hash_input.doc_type_offset);
    let valid_from_offset_in_preimage = offset(hash_input.valid_from_offset);
    let valid_until_offset_in_preimage = offset(hash_input.valid_until_offset);
    let dev_key_info_offset_in_preimage = offset(hash_input.dev_key_info_offset);
    let value_digests_offset_in_preimage = offset(hash_input.value_digests_offset);

    ConcreteGiven {
        hash_input,
        preimage,
        nblocks: nblocks.try_into().unwrap(),
        doc_type_offset_in_preimage,
        valid_from_offset_in_preimage,
        valid_until_offset_in_preimage,
        dev_key_info_offset_in_preimage,
        value_digests_offset_in_preimage,
        attribute_given,
    }
}

pub fn derived<const W: usize, N: Nat<W>>(given: &ConcreteGiven<N>) -> ConcreteDerived {
    let cose_sha_derived = crate::circuits::sha256msg::concrete::ConcreteDerived {
        sha_derived: crate::circuits::sha256msg::concrete::sha256_msg_derived(
            &given.preimage.value,
            &crate::circuits::sha256::constants::INITIAL,
            super::constants::K_MAX_SHA_BLOCKS,
        ),
    };

    let mut attribute_witnesses = Vec::with_capacity(given.attribute_given.len());
    for ag in &given.attribute_given {
        let attr_sha_derived = crate::circuits::sha256msg::concrete::ConcreteDerived {
            sha_derived: crate::circuits::sha256msg::concrete::sha256_msg_derived(
                &ag.padded_preimage,
                &crate::circuits::sha256::constants::INITIAL,
                2,
            ),
        };
        attribute_witnesses.push(AttrDerived {
            sha_derived: attr_sha_derived,
        });
    }

    ConcreteDerived {
        attribute_derived: attribute_witnesses,
        sha_derived: cose_sha_derived,
    }
}

pub fn hash_input_of_parsed_mdoc<const W: usize, N: Nat<W>>(
    parsed: &crate::mdoc::circuits::cbor::mdoc::ParsedMdoc<N>,
    req_attr_ids: &[&[u8]],
    now: &str,
) -> HashInput<N> {
    let attrs = req_attr_ids
        .iter()
        .map(|&req_id| {
            let a = parsed.get_attribute(req_id).unwrap_or_else(|| {
                panic!(
                    "Requested attribute {:?} not found in ParsedMdoc",
                    std::str::from_utf8(req_id).unwrap_or("<binary>")
                )
            });
            AttrInput {
                expected_name: crate::mdoc::circuits::cbor::encode_cbor_string(&a.name),
                expected_cbor_value: a.cbor_value.clone(),
                cbor_issuer_signed_item: a.cbor_issuer_signed_item.clone(),
                mso_digest_offset_in_preimage: a.mso_digest_offset_in_preimage,
                field_locator: a.field_locator,
            }
        })
        .collect();

    HashInput {
        attrs,
        now: now.as_bytes().to_vec(),
        suppress_doc_type_check: false,
        expected_doc_type: parsed.doc_type.as_bytes().to_vec(),
        cbor_mso: parsed.cbor_mso.clone(),
        issuer_sig_e: parsed.issuer_sig_digest.clone(),
        device_pk: parsed.device_pk.clone(),
        doc_type_offset: parsed.doc_type_offset_in_mso,
        valid_from_offset: parsed.valid_from_offset_in_mso,
        valid_until_offset: parsed.valid_until_offset_in_mso,
        dev_key_info_offset: parsed.device_key_info_offset_in_mso,
        value_digests_offset: parsed.value_digests_offset_in_mso,
    }
}
