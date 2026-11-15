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
        circuits::cbor::{encode_cbor_string, mdoc::compute_transcript_hash},
        proto::{
            hash::constants::{K_DOC_TYPE_BYTES, K_NAMESPACE_BYTES, K_TIMESTAMP_DIGITS},
            mso_attribute::constants::{K_ATTR_ID_BYTES, K_ATTR_INDEX_BITS, K_ATTR_VALUE_BYTES},
        },
        v2::{
            attribute::RequestedAttribute,
            inputs::builder::{AssignmentBuilder, BinaryAssignmentBuilder},
            request::Request,
        },
    },
    runtime::algebra::{
        p256::{P256Element, P256Field},
        RuntimeNat,
    },
};

/// The public inputs of both circuits (DESIGN.md I1), derived from a checked
/// request and nothing else. [`PublicInputs::derive`] is the only constructor.
pub(in crate::mdoc::runtime::v2) struct PublicInputs {
    hash: Vec<bool>,
    signature: Vec<P256Element>,
}

impl PublicInputs {
    /// Both roles' public inputs: the hash circuit's from the time, the
    /// attributes, the document type and the namespace, and the signature
    /// circuit's from the issuer key and `e2`, the digest of the
    /// `DeviceAuthentication` bytes for the session transcript and document type.
    pub(in crate::mdoc::runtime::v2) fn derive(request: &Request<'_>, p256: &P256Field) -> Self {
        let e2 = RuntimeNat::<4>::from_bytes_be(&compute_transcript_hash(
            request.transcript(),
            request.doc_type(),
        ));
        Self {
            hash: push_input_hash(
                request.attributes(),
                request.now().as_bytes(),
                request.doc_type().as_bytes(),
            ),
            signature: push_input_sig(p256, request.issuer_pk(), &e2),
        }
    }
    /// The hash circuit's public inputs.
    pub(in crate::mdoc::runtime::v2) fn hash(&self) -> &[bool] {
        &self.hash
    }
    /// The signature circuit's public inputs.
    pub(in crate::mdoc::runtime::v2) fn signature(&self) -> &[P256Element] {
        &self.signature
    }
}

fn push_input_attrs(builder: &mut BinaryAssignmentBuilder, attrs: &[RequestedAttribute]) {
    for la in attrs {
        let cbor_id = encode_cbor_string(&la.id);
        for i in 0..K_ATTR_ID_BYTES {
            builder.push_v8(*cbor_id.get(i).unwrap_or(&0));
        }
        builder.push_bits_len(cbor_id.len() as u64, K_ATTR_INDEX_BITS);

        for i in 0..K_ATTR_VALUE_BYTES {
            builder.push_v8(*la.cbor_value.get(i).unwrap_or(&0));
        }
        builder.push_bits_len(la.cbor_value.len() as u64, K_ATTR_INDEX_BITS);
    }
}

fn push_input_hash(
    attrs: &[RequestedAttribute],
    now_bytes: &[u8],
    expected_doc_type: &[u8],
) -> Vec<bool> {
    // v2 always checks the signed document type.
    const SUPPRESS_DOC_TYPE_CHECK: bool = false;
    let mut builder = BinaryAssignmentBuilder::new();
    for i in K_TIMESTAMP_DIGITS {
        builder.push_v8(*now_bytes.get(i).unwrap_or(&0));
    }

    push_input_attrs(&mut builder, attrs);

    builder.push_bit(SUPPRESS_DOC_TYPE_CHECK);
    for i in 0..K_DOC_TYPE_BYTES {
        builder.push_v8(*expected_doc_type.get(i).unwrap_or(&0));
    }
    builder.push_bits_len(expected_doc_type.len() as u64, K_ATTR_INDEX_BITS);
    let namespace = attrs
        .first()
        .map(|a| a.namespace_id.as_slice())
        .unwrap_or_default();
    for i in 0..K_NAMESPACE_BYTES {
        builder.push_v8(*namespace.get(i).unwrap_or(&0));
    }
    builder.push_bits_len(namespace.len() as u64, K_ATTR_INDEX_BITS);

    builder.buffer
}

fn push_input_sig<N: Nat<4>>(
    p256: &P256Field,
    issuer_pk: &(P256Element, P256Element),
    device_sig_e: &N,
) -> Vec<P256Element> {
    let mut builder = AssignmentBuilder::new(p256);
    builder.push_elt(&issuer_pk.0);
    builder.push_elt(&issuer_pk.1);

    builder.push_nat_256_bits(device_sig_e);

    builder.buffer
}
