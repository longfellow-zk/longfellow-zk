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

//! The checked mdoc v2 request (DESIGN.md I2). Both roles obtain a [`Request`]
//! only from [`Request::check`], and circuit loading, document parsing,
//! witness construction and public-input derivation take one, so none of them
//! runs on an unchecked request.

use crate::{
    mdoc::{
        circuits::cbor::{encode_cbor_string, parse::CborParser},
        proto::{
            hash::constants::{
                K_DOC_TYPE_BYTES, K_NAMESPACE_BYTES, K_TIMESTAMP_DIGITS, K_TIMESTAMP_LEN,
            },
            mso_attribute::constants::{K_ATTR_ID_BYTES, K_ATTR_VALUE_BYTES},
            NEXT_MAX_ATTRIBUTES,
        },
        v2::{
            attribute::{circuit_supports, same_namespace},
            key::parse_pk_coordinate,
            RequestedAttribute, ZkSpecStruct,
        },
    },
    runtime::algebra::p256::{P256Element, P256Field},
};

/// Why [`Request::check`] rejected a request: one variant per request row of
/// the error table in DESIGN.md. Each role maps it to its own error code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RequestError {
    /// The spec's version is not supported.
    Version,
    /// The number of requested attributes differs from the spec's.
    AttributeCount,
    /// Any other request-shape failure: namespaces differ, a field out of
    /// range or malformed, a session transcript that is not one CBOR item, a
    /// bad issuer key.
    Shape,
    /// A requested value is of a kind the circuit does not support.
    UnsupportedAttribute,
}

/// A request that passed every row of the request table. Its fields are
/// private and [`Request::check`] is its only constructor.
pub(super) struct Request<'a> {
    spec: &'a ZkSpecStruct,
    issuer_pk: (P256Element, P256Element),
    transcript: &'a [u8],
    attributes: &'a [RequestedAttribute],
    now: &'a str,
    doc_type: &'a str,
}

impl<'a> Request<'a> {
    /// Check a request, in the order of the error table: the spec version, the
    /// spec's attribute count against the supported range, the attribute
    /// count, a shared namespace, the session transcript, the public-input
    /// bounds and syntax, the attribute values, and the issuer key. Both
    /// roles run this before loading circuits or drawing randomness.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn check(
        spec: &'a ZkSpecStruct,
        pkx: &str,
        pky: &str,
        transcript: &'a [u8],
        attributes: &'a [RequestedAttribute],
        now: &'a str,
        doc_type: &'a str,
        p256: &P256Field,
    ) -> Result<Self, RequestError> {
        if !spec.supports_version() {
            return Err(RequestError::Version);
        }
        // The NEXT circuits exist for 1 to NEXT_MAX_ATTRIBUTES attributes; a
        // spec outside that range is a request-shape failure.
        if !(1..=NEXT_MAX_ATTRIBUTES).contains(&spec.num_attributes) {
            return Err(RequestError::Shape);
        }
        if attributes.len() != spec.num_attributes {
            return Err(RequestError::AttributeCount);
        }
        if !same_namespace(attributes)
            || !session_transcript_is_one_item(transcript)
            || !public_inputs_fit(attributes, now.as_bytes(), doc_type.as_bytes())
        {
            return Err(RequestError::Shape);
        }
        if !attributes.iter().all(|a| circuit_supports(&a.cbor_value)) {
            return Err(RequestError::UnsupportedAttribute);
        }
        let issuer_pk = (
            parse_pk_coordinate(pkx, p256).map_err(|_| RequestError::Shape)?,
            parse_pk_coordinate(pky, p256).map_err(|_| RequestError::Shape)?,
        );
        Ok(Self {
            spec,
            issuer_pk,
            transcript,
            attributes,
            now,
            doc_type,
        })
    }

    pub(super) fn spec(&self) -> &'a ZkSpecStruct {
        self.spec
    }
    /// The issuer key, parsed to canonical P-256 coordinates.
    pub(super) fn issuer_pk(&self) -> &(P256Element, P256Element) {
        &self.issuer_pk
    }
    /// The session transcript, one CBOR item.
    pub(super) fn transcript(&self) -> &'a [u8] {
        self.transcript
    }
    /// The requested attributes, all in one namespace.
    pub(super) fn attributes(&self) -> &'a [RequestedAttribute] {
        self.attributes
    }
    /// The current time, in the UTC syntax of [`timestamp_digits`].
    pub(super) fn now(&self) -> &'a str {
        self.now
    }
    pub(super) fn doc_type(&self) -> &'a str {
        self.doc_type
    }
}

/// Supported UTC spelling; T/t and Z/z have identical ordering semantics.
pub(super) fn timestamp_digits(value: &[u8]) -> Option<[u8; 14]> {
    if value.len() != K_TIMESTAMP_LEN
        || value[4] != b'-'
        || value[7] != b'-'
        || !matches!(value[10], b'T' | b't')
        || value[13] != b':'
        || value[16] != b':'
        || !matches!(value[19], b'Z' | b'z')
        || K_TIMESTAMP_DIGITS
            .iter()
            .any(|&i| !value[i].is_ascii_digit())
    {
        return None;
    }
    Some(K_TIMESTAMP_DIGITS.map(|i| value[i]))
}

/// Whether the session transcript is exactly one CBOR item. `e2` signs
/// `DeviceAuthentication`, where the transcript is followed directly by
/// `tstr(doc_type)`. A single item is self-delimiting, so the preimage
/// determines the (session transcript, document type) pair; empty, truncated,
/// concatenated or trailing bytes could shift that boundary.
fn session_transcript_is_one_item(transcript: &[u8]) -> bool {
    CborParser::new(transcript).parse_exact().is_ok()
}

/// Reject caller data that would be truncated by the fixed public-input slots.
/// Attribute counts are checked separately against the selected specification.
fn public_inputs_fit(attrs: &[RequestedAttribute], now: &[u8], doc_type: &[u8]) -> bool {
    timestamp_digits(now).is_some()
        && !doc_type.is_empty()
        && doc_type.len() <= K_DOC_TYPE_BYTES
        && attrs.first().is_some_and(|attribute| {
            !attribute.namespace_id.is_empty()
                && attribute.namespace_id.len() <= K_NAMESPACE_BYTES
                && std::str::from_utf8(&attribute.namespace_id).is_ok()
        })
        && attrs.iter().all(|attribute| {
            attribute.id.len() <= K_ATTR_ID_BYTES
                && encode_cbor_string(&attribute.id).len() <= K_ATTR_ID_BYTES
                && attribute.cbor_value.len() <= K_ATTR_VALUE_BYTES
        })
}

#[cfg(test)]
mod tests;
