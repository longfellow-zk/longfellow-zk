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

//! Longfellow v2 application attribute.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestedAttribute {
    /// All disclosures share this namespace. NEXT checks its exact text in the
    /// signed MSO; structural membership of the selected digests is not proved.
    pub namespace_id: Vec<u8>,
    pub id: Vec<u8>,
    /// The value's CBOR encoding, as it appears in the `IssuerSignedItem`.
    pub cbor_value: Vec<u8>,
}

/// A requested attribute: `namespace` and `id` are plain text, but
/// `encoded_cbor_value` is the value's raw CBOR encoding, copied as is, not
/// the value itself. Passing `"1"` requests the CBOR item `0x31`, the
/// integer -18, not the text `"1"` or the integer 1.
///
/// A text value carries its CBOR text header:
///
/// ```
/// use longfellow_zk::mdoc::v2::req_attr;
/// // "Erika": major type 3, length 5.
/// let attr = req_attr("org.iso.18013.5.1", "given_name", b"\x65Erika");
/// assert_eq!(attr.cbor_value, b"\x65Erika");
/// ```
///
/// An integer is its CBOR encoding, not its decimal digits:
///
/// ```
/// use longfellow_zk::mdoc::v2::req_attr;
/// // 1 is the single byte 0x01; 1984 is 0x19 then two bytes.
/// let one = req_attr("org.iso.18013.5.1", "age_in_years", [0x01]);
/// assert_eq!(one.cbor_value, [0x01]);
/// let year = req_attr("org.iso.18013.5.1", "age_birth_year", [0x19, 0x07, 0xc0]);
/// assert_eq!(year.cbor_value, [0x19, 0x07, 0xc0]);
/// ```
///
/// A boolean is the CBOR simple value `0xf5` (true) or `0xf4` (false):
///
/// ```
/// use longfellow_zk::mdoc::v2::req_attr;
/// let attr = req_attr("org.iso.18013.5.1", "age_over_18", [0xf5]);
/// assert_eq!(attr.cbor_value, [0xf5]);
/// ```
pub fn req_attr(
    namespace: impl AsRef<[u8]>,
    id: impl AsRef<[u8]>,
    encoded_cbor_value: impl AsRef<[u8]>,
) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: id.as_ref().to_vec(),
        cbor_value: encoded_cbor_value.as_ref().to_vec(),
    }
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[must_use]
pub(in crate::mdoc::runtime) fn same_namespace(attrs: &[RequestedAttribute]) -> bool {
    if attrs.is_empty() {
        return true;
    }
    let ns = &attrs[0].namespace_id;
    attrs.iter().all(|a| a.namespace_id == *ns)
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[must_use]
pub(in crate::mdoc::runtime) fn circuit_supports(data: &[u8]) -> bool {
    let mut parser = crate::mdoc::cbor::parse::CborParser::new(data);
    let Ok(el) = parser.parse_exact() else {
        return false;
    };
    match &el.value {
        crate::mdoc::cbor::parse::CborValue::Text(_)
        | crate::mdoc::cbor::parse::CborValue::Bytes(_)
        | crate::mdoc::cbor::parse::CborValue::Integer(_) => true,
        crate::mdoc::cbor::parse::CborValue::Simple(info) => *info == 20 || *info == 21,
        crate::mdoc::cbor::parse::CborValue::Tag(tag, inner) => match tag {
            1004 => {
                if data.len() != 14 {
                    return false;
                }
                matches!(inner.value, crate::mdoc::cbor::parse::CborValue::Text(_))
            }
            0 => {
                if data.len() != 22 {
                    return false;
                }
                matches!(inner.value, crate::mdoc::cbor::parse::CborValue::Text(_))
            }
            _ => false,
        },
        _ => false,
    }
}
