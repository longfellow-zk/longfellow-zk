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
    core::algebra::Nat,
    mdoc::{
        proto::{
            config::K_ATTR_LEN_BITS,
            hash::constants::{K_NAMESPACE_BYTES, K_TIMESTAMP_DIGITS, K_TIMESTAMP_LEN},
        },
        runtime::v2::{
            attribute::RequestedAttribute,
            inputs::builder::{AssignmentBuilder, BinaryAssignmentBuilder},
        },
    },
    runtime::algebra::p256::{P256Element, P256Field},
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
        && attrs.first().is_some_and(|attribute| {
            !attribute.namespace_id.is_empty()
                && attribute.namespace_id.len() <= K_NAMESPACE_BYTES
                && std::str::from_utf8(&attribute.namespace_id).is_ok()
        })
        && attrs.iter().all(|attribute| {
            attribute.id.len() <= ATTRIBUTE_ID_BYTES
                && crate::mdoc::circuits::cbor::encode_cbor_string(&attribute.id).len()
                    <= ATTRIBUTE_ID_BYTES
                && attribute.cbor_value.len() <= ATTRIBUTE_VALUE_BYTES
        })
}

fn push_input_attrs(builder: &mut BinaryAssignmentBuilder, attrs: &[RequestedAttribute]) {
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

pub(in crate::mdoc::runtime::v2) fn push_input_hash(
    attrs: &[RequestedAttribute],
    now_bytes: &[u8],
    suppress_doc_type_check: bool,
    expected_doc_type: &[u8],
) -> Vec<bool> {
    let mut builder = BinaryAssignmentBuilder::new();
    for i in K_TIMESTAMP_DIGITS {
        builder.push_v8(*now_bytes.get(i).unwrap_or(&0));
    }

    push_input_attrs(&mut builder, attrs);

    builder.push_bit(suppress_doc_type_check);
    for i in 0..DOC_TYPE_BYTES {
        builder.push_v8(*expected_doc_type.get(i).unwrap_or(&0));
    }
    builder.push_bits_len(expected_doc_type.len() as u64, K_ATTR_LEN_BITS);
    let namespace = attrs
        .first()
        .map(|a| a.namespace_id.as_slice())
        .unwrap_or_default();
    for i in 0..K_NAMESPACE_BYTES {
        builder.push_v8(*namespace.get(i).unwrap_or(&0));
    }
    builder.push_bits_len(namespace.len() as u64, K_ATTR_LEN_BITS);

    builder.into_inner()
}

pub(in crate::mdoc::runtime::v2) fn push_input_sig<N: Nat<4>>(
    p256: &P256Field,
    issuer_pk: &(P256Element, P256Element),
    device_sig_e: &N,
) -> Vec<P256Element> {
    let mut builder = AssignmentBuilder::new(p256);
    builder.push_elt(&issuer_pk.0);
    builder.push_elt(&issuer_pk.1);

    builder.push_nat_256_bits(device_sig_e);

    builder.into_inner()
}
