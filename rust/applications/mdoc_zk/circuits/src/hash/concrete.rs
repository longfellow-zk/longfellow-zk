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

use compile_algebra::CompileNat;
use core_algebra::Nat;

use super::constants::K_MSO_PREIMAGE_LEN;
use crate::mso_attribute::{
    concrete::FieldLocator as MsoFieldLocator,
    constants::{
        K_ELEMENT_VALUE_PREFIX, K_MAX_ATTR_SHA_BLOCKS, K_PNYM_SEED_LEN, K_PNYM_SHA_BLOCKS,
    },
};

#[derive(Clone, Debug)]
pub struct AttrInput {
    pub expected_name: Vec<u8>,
    pub expected_cbor_value: Vec<u8>,
    pub op: u8,
    pub cbor_issuer_signed_item: Vec<u8>,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
}

#[derive(Clone, Debug)]
pub struct PnymInput {
    pub expected_name: Vec<u8>,
    pub expected_cbor_value: Vec<u8>,
    pub context: Vec<u8>,
    pub cbor_issuer_signed_item: Vec<u8>,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
}

#[derive(Clone, Debug)]
pub struct HashMac {
    pub mac_av: u128,
    pub mac_ap: [[u128; 2]; 3],
}

#[derive(Clone, Debug)]
pub struct HashInput<N = CompileNat<4>> {
    pub attrs: Vec<AttrInput>,
    pub pnym: Option<PnymInput>,
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
    pub op: u8,
    pub padded_preimage: Vec<u8>,
    pub unpadded_preimage_len: usize,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
}

#[derive(Clone, Debug)]
pub struct AttrDerived {
    pub sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
}

#[derive(Clone, Debug)]
pub struct PnymGiven {
    pub expected_name: Vec<u8>,
    pub expected_cbor_value: Vec<u8>,
    pub context: Vec<u8>,
    pub padded_preimage: Vec<u8>,
    pub unpadded_preimage_len: usize,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: MsoFieldLocator,
    pub pnym_padded_preimage: Vec<u8>,
    pub pnym_length_bytes: usize,
    pub pnym_nblocks: usize,
}

#[derive(Clone, Debug)]
pub struct PnymDerived {
    pub item_sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
    pub pnym_sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
}

#[derive(Clone, Debug)]
pub struct ConcreteGiven<N = CompileNat<4>> {
    pub hash_input: HashInput<N>,
    pub mac_input: HashMac,
    pub mac_e: [u128; 2],
    pub mac_device_pkx: [u128; 2],
    pub mac_device_pky: [u128; 2],
    pub preimage: MsoPreimageBytes,
    pub nblocks: u8,
    pub doc_type_offset_in_preimage: u16,
    pub valid_from_offset_in_preimage: u16,
    pub valid_until_offset_in_preimage: u16,
    pub dev_key_info_offset_in_preimage: u16,
    pub value_digests_offset_in_preimage: u16,
    pub attribute_given: Vec<AttrGiven>,
    pub pnym_given: Option<PnymGiven>,
    pub mac_ap: [[u128; 2]; 3],
}

#[derive(Clone, Debug)]
pub struct ConcreteDerived {
    pub attribute_derived: Vec<AttrDerived>,
    pub pnym_derived: Option<PnymDerived>,
    pub sha_derived: circuits_sha256msg::concrete::ConcreteDerived,
}

pub fn compute_mac_tags<const W: usize, N: Nat<W>>(
    hash_input: &HashInput<N>,
    mac_input: &HashMac,
) -> ([u128; 2], [u128; 2], [u128; 2]) {
    let nat_to_32bytes = |n: &N| -> [u8; 32] {
        let bytes = n.to_bytes_le();
        assert!(bytes.len() <= 32);
        let mut padded = [0u8; 32];
        padded[..bytes.len()].copy_from_slice(&bytes);
        padded
    };

    let mac_e = circuits_mac::concrete::compute_tag(
        &nat_to_32bytes(&hash_input.issuer_sig_e),
        mac_input.mac_av,
        &mac_input.mac_ap[0],
    );
    let mac_device_pkx = circuits_mac::concrete::compute_tag(
        &nat_to_32bytes(&hash_input.device_pk.0),
        mac_input.mac_av,
        &mac_input.mac_ap[1],
    );
    let mac_device_pky = circuits_mac::concrete::compute_tag(
        &nat_to_32bytes(&hash_input.device_pk.1),
        mac_input.mac_av,
        &mac_input.mac_ap[2],
    );

    (mac_e, mac_device_pkx, mac_device_pky)
}

pub fn given<const W: usize, N: Nat<W>>(
    hash_input: HashInput<N>,
    mac_input: HashMac,
) -> ConcreteGiven<N> {
    let (mac_e, mac_device_pkx, mac_device_pky) = compute_mac_tags::<W, N>(&hash_input, &mac_input);

    let cose_sha_wit = circuits_sha256msg::concrete::given(
        &hash_input.cbor_mso,
        &circuits_sha256::constants::INITIAL,
        super::constants::K_MAX_SHA_BLOCKS,
    )
    .unwrap();
    let signed_bytes = cose_sha_wit.padded_preimage.clone();
    let nblocks = cose_sha_wit.nblocks;

    let preimage_base_offset = (super::constants::K_COSE1_PREFIX_LEN + 7) as u16;

    let mut attribute_given = Vec::with_capacity(hash_input.attrs.len());
    for a in &hash_input.attrs {
        let attr_sha_wit = circuits_sha256msg::concrete::given(
            &a.cbor_issuer_signed_item,
            &circuits_sha256::constants::INITIAL,
            K_MAX_ATTR_SHA_BLOCKS,
        )
        .unwrap();
        attribute_given.push(AttrGiven {
            expected_name: a.expected_name.clone(),
            expected_cbor_value: a.expected_cbor_value.clone(),
            op: a.op,
            padded_preimage: attr_sha_wit.padded_preimage,
            unpadded_preimage_len: a.cbor_issuer_signed_item.len(),
            mso_digest_offset_in_preimage: (preimage_base_offset
                + a.mso_digest_offset_in_preimage as u16)
                as usize,
            field_locator: a.field_locator,
        });
    }

    let pnym_given = hash_input.pnym.as_ref().map(|p| {
        let item_sha_wit = circuits_sha256msg::concrete::given(
            &p.cbor_issuer_signed_item,
            &circuits_sha256::constants::INITIAL,
            K_MAX_ATTR_SHA_BLOCKS,
        )
        .unwrap();
        // Locate the `elementValue` slot through the field locator and insist on exactly
        // what the circuit will enforce: `6c "elementValue" 58 20 || seed`. A malformed
        // fixture must fail here, loudly, rather than produce a witness with a zero seed
        // that only fails deep inside the circuit.
        let slot3_phys = (p.field_locator.permutation >> 6) & 3;
        let slot3_off = p.field_locator.slot_position[slot3_phys];
        let slot3_len = p.field_locator.length[slot3_phys];
        let slot = p
            .cbor_issuer_signed_item
            .get(slot3_off..slot3_off + slot3_len)
            .expect("pnym_seed elementValue slot lies outside the IssuerSignedItem");
        let (key, value) = slot.split_at(K_ELEMENT_VALUE_PREFIX.len().min(slot.len()));
        assert_eq!(
            key, K_ELEMENT_VALUE_PREFIX,
            "slot 3 is not the elementValue entry"
        );
        assert!(
            value.len() == 2 + K_PNYM_SEED_LEN && value[..2] == [0x58, 0x20],
            "pnym_seed elementValue must be a CBOR bstr(32) (`58 20 || seed`)"
        );
        let seed = &value[2..];
        let mut pnym_msg = Vec::with_capacity(K_PNYM_SEED_LEN + p.context.len());
        pnym_msg.extend_from_slice(seed);
        pnym_msg.extend_from_slice(&p.context);
        let pnym_sha_wit = circuits_sha256msg::concrete::given(
            &pnym_msg,
            &circuits_sha256::constants::INITIAL,
            K_PNYM_SHA_BLOCKS,
        )
        .unwrap();
        PnymGiven {
            expected_name: p.expected_name.clone(),
            expected_cbor_value: p.expected_cbor_value.clone(),
            context: p.context.clone(),
            padded_preimage: item_sha_wit.padded_preimage,
            unpadded_preimage_len: p.cbor_issuer_signed_item.len(),
            mso_digest_offset_in_preimage: (preimage_base_offset
                + p.mso_digest_offset_in_preimage as u16)
                as usize,
            field_locator: p.field_locator,
            pnym_padded_preimage: pnym_sha_wit.padded_preimage,
            pnym_length_bytes: pnym_msg.len(),
            pnym_nblocks: pnym_sha_wit.nblocks,
        }
    });

    let mut signed_bytes_arr = [0u8; K_MSO_PREIMAGE_LEN];
    let slen = std::cmp::min(signed_bytes.len(), K_MSO_PREIMAGE_LEN);
    signed_bytes_arr[..slen].copy_from_slice(&signed_bytes[..slen]);
    let preimage = MsoPreimageBytes {
        value: signed_bytes_arr,
        len: hash_input.cbor_mso.len() as u16,
    };

    let doc_type_offset_in_preimage = preimage_base_offset + hash_input.doc_type_offset as u16;
    let valid_from_offset_in_preimage = preimage_base_offset + hash_input.valid_from_offset as u16;
    let valid_until_offset_in_preimage =
        preimage_base_offset + hash_input.valid_until_offset as u16;
    let dev_key_info_offset_in_preimage =
        preimage_base_offset + hash_input.dev_key_info_offset as u16;
    let value_digests_offset_in_preimage =
        preimage_base_offset + hash_input.value_digests_offset as u16;

    ConcreteGiven {
        mac_ap: mac_input.mac_ap,
        hash_input,
        mac_input: mac_input.clone(),
        preimage,
        nblocks: nblocks.try_into().unwrap(),
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
    }
}

pub fn derived<const W: usize, N: Nat<W>>(given: &ConcreteGiven<N>) -> ConcreteDerived {
    let cose_sha_derived = circuits_sha256msg::concrete::ConcreteDerived {
        sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
            &given.preimage.value,
            &circuits_sha256::constants::INITIAL,
            super::constants::K_MAX_SHA_BLOCKS,
        ),
    };

    let mut attribute_witnesses = Vec::with_capacity(given.attribute_given.len());
    for ag in &given.attribute_given {
        let attr_sha_derived = circuits_sha256msg::concrete::ConcreteDerived {
            sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
                &ag.padded_preimage,
                &circuits_sha256::constants::INITIAL,
                K_MAX_ATTR_SHA_BLOCKS,
            ),
        };
        attribute_witnesses.push(AttrDerived {
            sha_derived: attr_sha_derived,
        });
    }

    let pnym_derived = given.pnym_given.as_ref().map(|pg| PnymDerived {
        item_sha_derived: circuits_sha256msg::concrete::ConcreteDerived {
            sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
                &pg.padded_preimage,
                &circuits_sha256::constants::INITIAL,
                K_MAX_ATTR_SHA_BLOCKS,
            ),
        },
        pnym_sha_derived: circuits_sha256msg::concrete::ConcreteDerived {
            sha_derived: circuits_sha256msg::concrete::sha256_msg_derived(
                &pg.pnym_padded_preimage,
                &circuits_sha256::constants::INITIAL,
                K_PNYM_SHA_BLOCKS,
            ),
        },
    });

    ConcreteDerived {
        attribute_derived: attribute_witnesses,
        pnym_derived,
        sha_derived: cose_sha_derived,
    }
}

pub fn hash_input_of_parsed_mdoc<const W: usize, N: Nat<W>>(
    parsed: &crate::cbor::mdoc::ParsedMdoc<N>,
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
                expected_name: crate::cbor::encode_cbor_string(&a.name),
                expected_cbor_value: a.cbor_value.clone(),
                op: 0,
                cbor_issuer_signed_item: a.cbor_issuer_signed_item.clone(),
                mso_digest_offset_in_preimage: a.mso_digest_offset_in_preimage,
                field_locator: a.field_locator,
            }
        })
        .collect();

    HashInput {
        attrs,
        pnym: None,
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

pub fn pnym_hash_input_of_parsed_mdoc<const W: usize, N: Nat<W>>(
    parsed: &crate::cbor::mdoc::ParsedMdoc<N>,
    context: &[u8],
    now: &str,
) -> HashInput<N> {
    let a = parsed
        .get_attribute(b"pnym_seed")
        .expect("pnym_seed attribute not found in ParsedMdoc");
    let seed = crate::cbor::mdoc::pnym_seed_of(a).expect("pnym_seed must be bstr(32)");
    let pnym_digest = crate::cbor::mdoc::compute_pseudonym(&seed, context);
    let expected_cbor_value = crate::cbor::mdoc::encode_pnym_cbor_value(&pnym_digest);

    HashInput {
        attrs: Vec::new(),
        pnym: Some(PnymInput {
            expected_name: crate::cbor::encode_cbor_string(&a.name),
            expected_cbor_value,
            context: context.to_vec(),
            cbor_issuer_signed_item: a.cbor_issuer_signed_item.clone(),
            mso_digest_offset_in_preimage: a.mso_digest_offset_in_preimage,
            field_locator: a.field_locator,
        }),
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

impl ConcreteDerived {
    #[cfg(feature = "testonly")]
    pub fn push_derived<const W: usize, FR: runtime_algebra::field::RuntimeField<W>>(
        &self,
        fr: &FR,
        mut push: impl FnMut(FR::E),
    ) {
        for attr_wit in &self.attribute_derived {
            attr_wit.sha_derived.push_derived(fr, &mut push);
        }
        if let Some(ref pnym_wit) = self.pnym_derived {
            pnym_wit.item_sha_derived.push_derived(fr, &mut push);
            pnym_wit.pnym_sha_derived.push_derived(fr, &mut push);
        }
        self.sha_derived.push_derived(fr, &mut push);
    }
}
