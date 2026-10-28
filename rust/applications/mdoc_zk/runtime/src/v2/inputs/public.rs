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

//! Longfellow v2 public assignment encoding.

use crate::{
    core::algebra::{AlgebraicField, Nat, SupportsU64Conversions},
    mdoc::{
        proto::{config::K_ATTR_LEN_BITS, hash::constants::K_TIMESTAMP_LEN},
        runtime::v2::{attribute::RequestedAttribute, inputs::builder::AssignmentBuilder},
    },
    runtime::algebra::{
        gf2_128::{Gf2_128, Gf2_128Field},
        p256::{P256Element, P256Field},
    },
};

const ATTRIBUTE_ID_BYTES: usize = 32;
const ATTRIBUTE_VALUE_BYTES: usize = 64;
const DOC_TYPE_BYTES: usize = 32;

/// Reject caller data that would be truncated by the fixed public-input slots.
/// Both roles check these bounds before allocating witnesses or decoding proofs.
/// Attribute counts are checked separately against the selected specification.
pub(in crate::mdoc::runtime::v2) fn public_inputs_fit(
    attrs: &[RequestedAttribute],
    now: &[u8],
    doc_type: &[u8],
) -> bool {
    now.len() == K_TIMESTAMP_LEN
        && doc_type.len() <= DOC_TYPE_BYTES
        && attrs.iter().all(|attribute| {
            attribute.id.len() <= ATTRIBUTE_ID_BYTES
                && crate::mdoc::circuits::cbor::encode_cbor_string(&attribute.id).len()
                    <= ATTRIBUTE_ID_BYTES
                && attribute.cbor_value.len() <= ATTRIBUTE_VALUE_BYTES
        })
}

fn push_input_attrs(
    builder: &mut AssignmentBuilder<'_, Gf2_128Field>,
    attrs: &[RequestedAttribute],
) {
    for la in attrs {
        let cbor_id = crate::mdoc::circuits::cbor::encode_cbor_string(&la.id);
        for i in 0..ATTRIBUTE_ID_BYTES {
            builder.push_v8(*cbor_id.get(i).unwrap_or(&0));
        }
        builder.push_bits_len(cbor_id.len() as u64, K_ATTR_LEN_BITS);

        for i in 0..ATTRIBUTE_VALUE_BYTES {
            builder.push_v8(*la.cbor_value.get(i).unwrap_or(&0));
        }
        builder.push_bits_len(la.cbor_value.len() as u64, K_ATTR_LEN_BITS);
    }
}

fn build_input_hash<'a>(
    mut builder: AssignmentBuilder<'a, Gf2_128Field>,
    attrs: &[RequestedAttribute],
    now_bytes: &[u8],
    macs: &[u128; 6],
    av: u128,
    suppress_doc_type_check: bool,
    expected_doc_type: &[u8],
) -> AssignmentBuilder<'a, Gf2_128Field> {
    let gf2 = builder.field;
    builder.push_elt(&gf2.one());
    for i in 0..K_TIMESTAMP_LEN {
        builder.push_v8(*now_bytes.get(i).unwrap_or(&0));
    }

    push_input_attrs(&mut builder, attrs);

    for &m in macs {
        builder.push_mac_field(m);
    }
    builder.push_mac_field(av);

    let suppress_val = if suppress_doc_type_check {
        gf2.one()
    } else {
        gf2.zero()
    };
    builder.push_elt(&suppress_val);
    for i in 0..DOC_TYPE_BYTES {
        builder.push_v8(*expected_doc_type.get(i).unwrap_or(&0));
    }
    builder.push_bits_len(expected_doc_type.len() as u64, K_ATTR_LEN_BITS);

    builder
}

pub(in crate::mdoc::runtime::v2) fn push_input_hash(
    gf2: &Gf2_128Field,
    attrs: &[RequestedAttribute],
    now_bytes: &[u8],
    macs: &[u128; 6],
    av: u128,
    suppress_doc_type_check: bool,
    expected_doc_type: &[u8],
) -> Vec<Gf2_128> {
    build_input_hash(
        AssignmentBuilder::new(gf2),
        attrs,
        now_bytes,
        macs,
        av,
        suppress_doc_type_check,
        expected_doc_type,
    )
    .into_inner()
}
#[cfg(feature = "experimental")]
pub(in crate::mdoc::runtime::v2) fn push_input_hash_boolean(
    gf2: &Gf2_128Field,
    attrs: &[RequestedAttribute],
    now_bytes: &[u8],
    macs: &[u128; 6],
    av: u128,
    suppress_doc_type_check: bool,
    expected_doc_type: &[u8],
) -> Vec<Gf2_128> {
    build_input_hash(
        AssignmentBuilder::new_boolean(gf2),
        attrs,
        now_bytes,
        macs,
        av,
        suppress_doc_type_check,
        expected_doc_type,
    )
    .into_inner()
}

pub(in crate::mdoc::runtime::v2) fn push_input_sig<N: Nat<4>>(
    p256: &P256Field,
    issuer_pk: &(P256Element, P256Element),
    device_sig_e: &N,
    macs: &[u128; 6],
    av: u128,
) -> Vec<P256Element> {
    let mut builder = AssignmentBuilder::new(p256);
    builder.push_elt(&p256.u64_to_element(1));
    builder.push_elt(&issuer_pk.0);
    builder.push_elt(&issuer_pk.1);

    builder.push_nat_256_bits(device_sig_e);

    for &m in macs {
        builder.push_plucked_128(m);
    }
    builder.push_plucked_128(av);
    builder.into_inner()
}
