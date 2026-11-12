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
    core::algebra::Nat,
    mdoc::circuits::cbor::{
        append_bytes_len, append_text_len,
        constants::{
            K_COSE1_PREFIX_LEN, K_COSE_SIGN1_SIGNING_HEADER, K_DEVICE_AUTHENTICATION_HEADER,
            K_TAG24,
        },
        parse::{CborElement, CborIndexVal, CborParser, CborValue},
    },
};

#[derive(Clone, Copy, Debug)]
pub struct FieldLocator {
    pub slot_position: [usize; 4],
    pub length: [usize; 4],
    pub permutation: usize,
}

#[derive(Clone, Debug)]
pub struct ParsedAttr {
    pub name: Vec<u8>,
    pub cbor_value: Vec<u8>,
    pub cbor_issuer_signed_item: Vec<u8>,
    pub mso_digest_offset_in_preimage: usize,
    pub field_locator: FieldLocator,
}

#[derive(Clone, Debug)]
pub struct DeviceKeyInfo {
    pub key_type: i64,
    pub crv: i64,
    pub x: Vec<u8>,
    pub y: Vec<u8>,
}

#[derive(Clone, Debug)]
pub struct ParsedMdoc<N> {
    pub issuer_sig_digest: N,
    pub issuer_sig_r: N,
    pub issuer_sig_s: N,
    pub device_pk: (N, N),
    pub device_sig_digest: N,
    pub device_sig_r: N,
    pub device_sig_s: N,
    pub doc_type: String,
    pub doc_type_offset_in_mso: usize,
    pub valid_from_offset_in_mso: usize,
    pub valid_until_offset_in_mso: usize,
    pub device_key_info_offset_in_mso: usize,
    pub value_digests_offset_in_mso: usize,
    pub attrs: Vec<ParsedAttr>,
    pub cbor_mso: Vec<u8>,
}

/// Host-side namespace selection. This metadata is not a circuit proof of
/// container membership; the circuit separately checks the selected text bytes.
#[cfg(any(test, feature = "prover"))]
pub(crate) struct MsoNamespace {
    pub name: Vec<u8>,
    /// Offsets are relative to the MSO map, like the parsed attribute digests.
    /// The witness encoder adds the signed-message envelope separately.
    pub key_offset: usize,
    pub digest_range: std::ops::Range<usize>,
}

impl<N> ParsedMdoc<N> {
    pub fn all_attr_ids(&self) -> Vec<&[u8]> {
        self.attrs.iter().map(|a| a.name.as_slice()).collect()
    }

    pub fn get_attribute(&self, name: &[u8]) -> Option<&ParsedAttr> {
        self.attrs.iter().find(|a| a.name == name)
    }

    /// Recover the namespace keys and their digest-map ranges without changing
    /// the legacy parser or its attribute representation.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn namespaces(&self) -> Result<Vec<MsoNamespace>, MdocParseError> {
        let map_bytes = self
            .cbor_mso
            .get(K_COSE1_PREFIX_LEN + 7..)
            .ok_or(MdocParseError::UnsupportedEncoding)?;
        let map = CborParser::new(map_bytes)
            .parse_exact()
            .map_err(|message| MdocParseError::Cbor {
                context: "MSO namespace map",
                message,
            })?;
        let (_, digests) = map_entry_unique(&map, "valueDigests", "MSO.valueDigests")?;
        let CborValue::Map(entries) = &digests.value else {
            return Err(MdocParseError::UnexpectedType("MSO.valueDigests"));
        };
        let mut namespaces = Vec::with_capacity(entries.len());
        for (key, value) in entries {
            let CborValue::Text(name) = &key.value else {
                return Err(MdocParseError::UnexpectedType("MSO namespace name"));
            };
            if !matches!(value.value, CborValue::Map(_)) {
                return Err(MdocParseError::UnexpectedType("MSO namespace digests"));
            }
            if namespaces
                .iter()
                .any(|ns: &MsoNamespace| ns.name == name.as_bytes())
            {
                return Err(MdocParseError::DuplicateField("MSO namespace"));
            }
            namespaces.push(MsoNamespace {
                name: name.as_bytes().to_vec(),
                key_offset: key.start,
                digest_range: value.start..value.end,
            });
        }
        Ok(namespaces)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocParseError {
    Cbor {
        context: &'static str,
        message: String,
    },
    MissingField(&'static str),
    DuplicateField(&'static str),
    UnexpectedType(&'static str),
    InvalidLength {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    InvalidValue(&'static str),
    UnknownField(String),
    UnsupportedEncoding,
    TooBig,
    ArithmeticOverflow(&'static str),
}

impl core::fmt::Display for MdocParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Cbor { context, message } => {
                write!(f, "failed to decode {context}: {message}")
            }
            Self::MissingField(field) => write!(f, "missing field: {field}"),
            Self::DuplicateField(field) => write!(f, "duplicate field: {field}"),
            Self::UnexpectedType(field) => write!(f, "unexpected CBOR type for {field}"),
            Self::InvalidLength {
                field,
                expected,
                actual,
            } => write!(
                f,
                "invalid length for {field}: expected {expected}, got {actual}"
            ),
            Self::InvalidValue(field) => write!(f, "invalid value for {field}"),
            Self::UnknownField(field) => write!(f, "unknown field: {field}"),
            Self::UnsupportedEncoding => {
                write!(f, "MSO encoding is not supported by the circuit")
            }
            Self::TooBig => write!(f, "MSO exceeds the circuit's SHA-256 capacity"),
            Self::ArithmeticOverflow(context) => {
                write!(f, "arithmetic overflow while computing {context}")
            }
        }
    }
}

impl std::error::Error for MdocParseError {}

pub fn parse_mdoc<N: Nat<4>>(
    mdoc: &[u8],
    transcript: &[u8],
    doc_type: &str,
) -> Result<ParsedMdoc<N>, MdocParseError> {
    parse_mdoc_with_mso_check(mdoc, transcript, doc_type, |_| Ok(()))
}

/// Preserve legacy parsing while allowing v2 to validate the original MSO
/// values before fixed-width integer conversion or witness construction.
pub(in crate::mdoc) fn parse_mdoc_with_mso_check<N: Nat<4>, E: From<MdocParseError>>(
    mdoc: &[u8],
    transcript: &[u8],
    doc_type: &str,
    check_mso: impl FnOnce(&CborElement) -> Result<(), E>,
) -> Result<ParsedMdoc<N>, E> {
    use sha2::{Digest, Sha256};

    let mut root_parser = CborParser::new(mdoc);
    let root = root_parser
        .parse_exact()
        .map_err(|message| MdocParseError::Cbor {
            context: "root mdoc",
            message,
        })?;

    let docs_el = required_map_value(&root, "documents", "root.documents")?;
    let docs_arr = required_array(&docs_el, "root.documents")?;
    let doc0 = docs_arr
        .first()
        .ok_or(MdocParseError::MissingField("root.documents[0]"))?;

    // Traverse issuerSigned -> issuerAuth to find MSO and issuer signature
    let issuer_signed = required_map_value(doc0, "issuerSigned", "documents[0].issuerSigned")?;
    let issuer_auth = required_map_value(
        &issuer_signed,
        "issuerAuth",
        "documents[0].issuerSigned.issuerAuth",
    )?;
    let issuer_auth_arr =
        required_cose_sign1_array(&issuer_auth, "documents[0].issuerSigned.issuerAuth")?;

    // MSO is the third element of the COSE_Sign1 structure in issuerAuth
    let cbor_mso_wrapped = required_bytes(
        issuer_auth_arr
            .get(2)
            .ok_or(MdocParseError::MissingField("issuerAuth payload"))?,
        "issuerAuth payload",
    )?
    .clone();

    // Unwrap the Tag 24 wrapping the MSO Map
    let mut mso_unwrap_parser = CborParser::new(&cbor_mso_wrapped);
    let mso_val = mso_unwrap_parser
        .parse_exact()
        .map_err(|message| MdocParseError::Cbor {
            context: "wrapped MSO",
            message,
        })?;
    let cbor_mso_map_bytes = if let CborValue::Tag(24, ref bstr_el) = mso_val.value {
        if let CborValue::Bytes(ref b) = bstr_el.value {
            b.clone()
        } else {
            return Err(MdocParseError::UnexpectedType("tag-24 MSO payload").into());
        }
    } else {
        return Err(MdocParseError::InvalidValue("MSO tag").into());
    };

    validate_mso_layout(&cbor_mso_wrapped, &cbor_mso_map_bytes)?;

    // Calculate signed message hash `issuer_sig_digest` on the MSO bytes
    let cbor_mso = format_cose_sign1_message(&cbor_mso_wrapped);
    let mut hasher = Sha256::new();
    hasher.update(&cbor_mso);
    let issuer_sig_digest = N::from_bytes_be(&hasher.finalize());

    let mut map_parser = CborParser::new(&cbor_mso_map_bytes);
    let mso_map = map_parser
        .parse_exact()
        .map_err(|message| MdocParseError::Cbor {
            context: "MSO map",
            message,
        })?;
    check_mso(&mso_map)?;
    let dev_key_info_el = required_map_value(&mso_map, "deviceKeyInfo", "MSO.deviceKeyInfo")?;
    let dev_key_el =
        required_map_value(&dev_key_info_el, "deviceKey", "MSO.deviceKeyInfo.deviceKey")?;

    // Extract device public key coordinates (keep original big-endian
    // coordinates)
    let dpkx_bytes = required_device_coordinate(&dev_key_el, -2, "MSO.deviceKeyInfo.deviceKey.x")?;
    let dpkx = N::from_bytes_be(&dpkx_bytes);
    let dpky_bytes = required_device_coordinate(&dev_key_el, -3, "MSO.deviceKeyInfo.deviceKey.y")?;
    let dpky = N::from_bytes_be(&dpky_bytes);

    // Issuer signature is the fourth element of issuerAuth COSE_Sign1 structure
    let issuer_sig_bytes = required_bytes(
        issuer_auth_arr
            .get(3)
            .ok_or(MdocParseError::MissingField("issuer signature"))?,
        "issuer signature",
    )?;
    let (issuer_sig_r, issuer_sig_s) = parse_signature(issuer_sig_bytes, "issuer signature")?;

    // Traverse deviceSigned -> deviceAuth -> deviceSignature to get device
    // signature
    let device_signed = required_map_value(doc0, "deviceSigned", "documents[0].deviceSigned")?;
    let device_auth = required_map_value(
        &device_signed,
        "deviceAuth",
        "documents[0].deviceSigned.deviceAuth",
    )?;
    let device_signature = required_map_value(
        &device_auth,
        "deviceSignature",
        "documents[0].deviceSigned.deviceAuth.deviceSignature",
    )?;
    let device_signature_arr = required_cose_sign1_array(
        &device_signature,
        "documents[0].deviceSigned.deviceAuth.deviceSignature",
    )?;

    // Device signature is the fourth element of deviceSignature COSE_Sign1
    // structure
    let device_sig_bytes = required_bytes(
        device_signature_arr
            .get(3)
            .ok_or(MdocParseError::MissingField("device signature"))?,
        "device signature",
    )?;
    let (device_sig_r, device_sig_s) = parse_signature(device_sig_bytes, "device signature")?;

    let hash_tr_bytes = compute_transcript_hash(transcript, doc_type);
    let device_sig_digest = N::from_bytes_be(&hash_tr_bytes);

    // Locate offset indices in raw CBOR map_bytes for MSO fields
    let doc_type_entry = required_map_key(&mso_map, "docType", "MSO.docType")?;
    let validity_info = required_map_value(&mso_map, "validityInfo", "MSO.validityInfo")?;
    let valid_from = required_map_key(&validity_info, "validFrom", "MSO.validityInfo.validFrom")?;
    let valid_until =
        required_map_key(&validity_info, "validUntil", "MSO.validityInfo.validUntil")?;
    let device_key_info = required_map_key(&mso_map, "deviceKeyInfo", "MSO.deviceKeyInfo")?;
    let value_digests = required_map_key(&mso_map, "valueDigests", "MSO.valueDigests")?;
    let value_digests_el = required_map_value(&mso_map, "valueDigests", "MSO.valueDigests")?;

    let attrs = extract_attrs(&issuer_signed, mdoc, &value_digests_el)?;

    Ok(ParsedMdoc {
        cbor_mso,
        issuer_sig_digest,
        issuer_sig_r,
        issuer_sig_s,
        device_pk: (dpkx, dpky),
        device_sig_digest,
        device_sig_r,
        device_sig_s,
        doc_type: doc_type.to_string(),
        doc_type_offset_in_mso: doc_type_entry.k,
        valid_from_offset_in_mso: valid_from.k,
        valid_until_offset_in_mso: valid_until.k,
        device_key_info_offset_in_mso: device_key_info.k,
        value_digests_offset_in_mso: value_digests.k,
        attrs,
    })
}

pub(in crate::mdoc) fn map_entry_unique<'a>(
    map: &'a CborElement,
    key: &str,
    path: &'static str,
) -> Result<(&'a CborElement, &'a CborElement), MdocParseError> {
    let pairs = if let CborValue::Map(pairs) = &map.value {
        pairs
    } else {
        return Err(MdocParseError::UnexpectedType(path));
    };

    let mut found = None;
    for (candidate_key, value) in pairs {
        if matches!(&candidate_key.value, CborValue::Text(text) if text == key) {
            if found.is_some() {
                return Err(MdocParseError::DuplicateField(path));
            }
            found = Some((candidate_key, value));
        }
    }
    found.ok_or(MdocParseError::MissingField(path))
}

fn required_map_value(
    map: &CborElement,
    key: &str,
    path: &'static str,
) -> Result<CborElement, MdocParseError> {
    let (_, value) = map_entry_unique(map, key, path)?;
    Ok(value.clone())
}

fn required_map_key(
    map: &CborElement,
    key: &str,
    path: &'static str,
) -> Result<CborIndexVal, MdocParseError> {
    let (key_element, value) = map_entry_unique(map, key, path)?;
    Ok(CborIndexVal {
        k: key_element.start,
        v: value.start,
    })
}

fn required_array<'a>(
    element: &'a CborElement,
    field: &'static str,
) -> Result<&'a Vec<CborElement>, MdocParseError> {
    if let CborValue::Array(array) = &element.value {
        Ok(array)
    } else {
        Err(MdocParseError::UnexpectedType(field))
    }
}

fn required_cose_sign1_array<'a>(
    element: &'a CborElement,
    field: &'static str,
) -> Result<&'a Vec<CborElement>, MdocParseError> {
    match &element.value {
        CborValue::Array(array) => Ok(array),
        CborValue::Tag(18, inner) => required_array(inner, field),
        _ => Err(MdocParseError::UnexpectedType(field)),
    }
}

fn required_bytes<'a>(
    element: &'a CborElement,
    field: &'static str,
) -> Result<&'a Vec<u8>, MdocParseError> {
    if let CborValue::Bytes(bytes) = &element.value {
        Ok(bytes)
    } else {
        Err(MdocParseError::UnexpectedType(field))
    }
}

fn required_tagged_bytes<'a>(
    element: &'a CborElement,
    tag: u64,
    field: &'static str,
) -> Result<&'a Vec<u8>, MdocParseError> {
    if let CborValue::Tag(actual_tag, inner) = &element.value {
        if *actual_tag == tag {
            return required_bytes(inner, field);
        }
    }
    Err(MdocParseError::UnexpectedType(field))
}

fn required_device_coordinate(
    device_key: &CborElement,
    coordinate_key: i128,
    field: &'static str,
) -> Result<Vec<u8>, MdocParseError> {
    let pairs = if let CborValue::Map(pairs) = &device_key.value {
        pairs
    } else {
        return Err(MdocParseError::UnexpectedType(
            "MSO.deviceKeyInfo.deviceKey",
        ));
    };

    let mut found = None;
    for (key, value) in pairs {
        if matches!(key.value, CborValue::Integer(parsed_key) if parsed_key == coordinate_key) {
            if found.is_some() {
                return Err(MdocParseError::DuplicateField(field));
            }
            found = Some(required_bytes(value, field)?.clone());
        }
    }
    found.ok_or(MdocParseError::MissingField(field))
}

fn required_digest_offset(
    value_digests: &CborElement,
    namespace: &str,
    digest_id: u64,
) -> Result<usize, MdocParseError> {
    let namespace_map = required_map_value(value_digests, namespace, "MSO.valueDigests namespace")?;
    let pairs = if let CborValue::Map(pairs) = &namespace_map.value {
        pairs
    } else {
        return Err(MdocParseError::UnexpectedType("MSO.valueDigests namespace"));
    };

    let mut found = None;
    for (key, value) in pairs {
        if matches!(key.value, CborValue::Integer(id) if id == i128::from(digest_id)) {
            if found.is_some() {
                return Err(MdocParseError::DuplicateField("attribute digest in MSO"));
            }
            found = Some(value.start);
        }
    }
    found.ok_or(MdocParseError::MissingField("attribute digest in MSO"))
}

fn parse_signature<N: Nat<4>>(bytes: &[u8], field: &'static str) -> Result<(N, N), MdocParseError> {
    if bytes.len() != 64 {
        return Err(MdocParseError::InvalidLength {
            field,
            expected: 64,
            actual: bytes.len(),
        });
    }
    let (r, s) = bytes.split_at(32);
    Ok((N::from_bytes_be(r), N::from_bytes_be(s)))
}

fn validate_mso_layout(
    cbor_mso_wrapped: &[u8],
    cbor_mso_map_bytes: &[u8],
) -> Result<(), MdocParseError> {
    // SHA-256 padding needs one marker byte and an eight-byte length suffix.
    let max_preimage_len = crate::mdoc::proto::hash::constants::K_MSO_PREIMAGE_LEN - 9;
    let formatted_len = K_COSE1_PREFIX_LEN
        .checked_add(2)
        .and_then(|len| len.checked_add(cbor_mso_wrapped.len()))
        .ok_or(MdocParseError::TooBig)?;
    if formatted_len > max_preimage_len || cbor_mso_wrapped.len() > u16::MAX as usize {
        return Err(MdocParseError::TooBig);
    }

    // NEXT circuits assume the deterministic encoding
    // tag(24) + bytes(u16 length) + MSO map bytes.
    if cbor_mso_map_bytes.len() < 256
        || cbor_mso_wrapped.get(..3) != Some(&[0xd8, 0x18, 0x59])
        || cbor_mso_wrapped.len() != cbor_mso_map_bytes.len() + 5
    {
        return Err(MdocParseError::UnsupportedEncoding);
    }

    let encoded_map_len = u16::from_be_bytes([cbor_mso_wrapped[3], cbor_mso_wrapped[4]]) as usize;
    if encoded_map_len != cbor_mso_map_bytes.len() {
        return Err(MdocParseError::UnsupportedEncoding);
    }

    Ok(())
}

fn extract_attrs(
    issuer_signed: &CborElement,
    mdoc_bytes: &[u8],
    value_digests: &CborElement,
) -> Result<Vec<ParsedAttr>, MdocParseError> {
    let mut attrs = Vec::new();
    let namespaces_el = required_map_value(
        issuer_signed,
        "nameSpaces",
        "documents[0].issuerSigned.nameSpaces",
    )?;
    let ns_pairs = if let CborValue::Map(ns_pairs) = &namespaces_el.value {
        ns_pairs
    } else {
        return Err(MdocParseError::UnexpectedType("nameSpaces"));
    };

    let mut namespace_names = std::collections::HashSet::new();
    for (ns_key, ns_val) in ns_pairs {
        let ns_name = if let CborValue::Text(name) = &ns_key.value {
            name.as_str()
        } else {
            return Err(MdocParseError::UnexpectedType("namespace name"));
        };
        if !namespace_names.insert(ns_name) {
            return Err(MdocParseError::DuplicateField(
                "documents[0].issuerSigned.nameSpaces namespace",
            ));
        }
        let items_arr = required_array(ns_val, "namespace items")?;
        let mut element_identifiers = std::collections::HashSet::new();
        for signed_item_el in items_arr {
            // Extracts the raw IssuerSignedItem bytes wrapped in Tag 24.
            let cbor_issuer_signed_item_wrapped = mdoc_bytes
                .get(signed_item_el.start..signed_item_el.end)
                .ok_or(MdocParseError::InvalidValue("IssuerSignedItem byte range"))?;
            let cbor_issuer_signed_item_map =
                required_tagged_bytes(signed_item_el, 24, "IssuerSignedItem tag-24 payload")?;
            let mut attr_parser = CborParser::new(cbor_issuer_signed_item_map);
            let signed_item =
                attr_parser
                    .parse_exact()
                    .map_err(|message| MdocParseError::Cbor {
                        context: "IssuerSignedItem map",
                        message,
                    })?;

            let element_id_el = required_map_value(
                &signed_item,
                "elementIdentifier",
                "IssuerSignedItem.elementIdentifier",
            )?;
            let element_id = if let CborValue::Text(id) = &element_id_el.value {
                id
            } else {
                return Err(MdocParseError::UnexpectedType("elementIdentifier"));
            };
            if !element_identifiers.insert(element_id.clone()) {
                return Err(MdocParseError::DuplicateField(
                    "namespace elementIdentifier",
                ));
            }
            let element_value_el = required_map_value(
                &signed_item,
                "elementValue",
                "IssuerSignedItem.elementValue",
            )?;
            let cbor_value = cbor_issuer_signed_item_map
                .get(element_value_el.start..element_value_el.end)
                .ok_or(MdocParseError::InvalidValue("elementValue byte range"))?;

            let witness = compute_witness(
                element_id.as_bytes().to_vec(),
                cbor_value.to_vec(),
                cbor_issuer_signed_item_wrapped,
                &signed_item,
                value_digests,
                ns_name,
            )?;

            attrs.push(witness);
        }
    }
    Ok(attrs)
}

fn compute_witness(
    name: Vec<u8>,
    cbor_value: Vec<u8>,
    cbor_issuer_signed_item: &[u8],
    inner_map: &CborElement,
    value_digests: &CborElement,
    namespace: &str,
) -> Result<ParsedAttr, MdocParseError> {
    // Match AttributeVerifier's fixed Tag-24, one-byte byte-string length,
    // and four-entry map prefix before constructing any layout witness.
    if cbor_issuer_signed_item.get(..3) != Some(&[0xd8, 0x18, 0x58])
        || cbor_issuer_signed_item.get(4) != Some(&0xa4)
        || cbor_issuer_signed_item.len() != 4 + usize::from(cbor_issuer_signed_item[3])
    {
        return Err(MdocParseError::UnsupportedEncoding);
    }
    let pairs = if let CborValue::Map(pairs) = &inner_map.value {
        pairs
    } else {
        return Err(MdocParseError::UnexpectedType("IssuerSignedItem map"));
    };
    if pairs.len() != 4 {
        return Err(MdocParseError::InvalidLength {
            field: "IssuerSignedItem map",
            expected: 4,
            actual: pairs.len(),
        });
    }

    let mut slots = [None; 4];

    let mut length = [0usize; 4];
    let mut digest_id = None;

    for (i, (k, v)) in pairs.iter().enumerate() {
        let key_str = if let CborValue::Text(s) = &k.value {
            s
        } else {
            return Err(MdocParseError::UnexpectedType("IssuerSignedItem key"));
        };

        // The circuit matches literal one-byte text headers for these keys.
        if k.end.checked_sub(k.start) != Some(1 + key_str.len()) {
            return Err(MdocParseError::UnsupportedEncoding);
        }

        length[i] = v
            .end
            .checked_sub(k.start)
            .ok_or(MdocParseError::ArithmeticOverflow(
                "IssuerSignedItem field length",
            ))?;

        match key_str.as_str() {
            "digestID" => {
                if slots[0].is_some() {
                    return Err(MdocParseError::DuplicateField("IssuerSignedItem.digestID"));
                }
                slots[0] = Some(i);
                if let CborValue::Integer(n) = v.value {
                    // The circuit's atomic decoder excludes eight-byte IDs.
                    if cbor_issuer_signed_item.get(4 + v.start) == Some(&0x1b) {
                        return Err(MdocParseError::UnsupportedEncoding);
                    }
                    digest_id = Some(
                        u64::try_from(n).map_err(|_| MdocParseError::InvalidValue("digestID"))?,
                    );
                } else {
                    return Err(MdocParseError::UnexpectedType("digestID"));
                }
            }
            "random" => {
                if !matches!(v.value, CborValue::Bytes(_)) {
                    return Err(MdocParseError::UnexpectedType("IssuerSignedItem.random"));
                }
                // Structured lengths in the circuit use at most one length byte.
                if cbor_issuer_signed_item[4 + v.start] > 0x58 {
                    return Err(MdocParseError::UnsupportedEncoding);
                }
                if slots[1].replace(i).is_some() {
                    return Err(MdocParseError::DuplicateField("IssuerSignedItem.random"));
                }
            }
            "elementIdentifier" => {
                if slots[2].replace(i).is_some() {
                    return Err(MdocParseError::DuplicateField(
                        "IssuerSignedItem.elementIdentifier",
                    ));
                }
            }
            "elementValue" => {
                if slots[3].replace(i).is_some() {
                    return Err(MdocParseError::DuplicateField(
                        "IssuerSignedItem.elementValue",
                    ));
                }
            }
            _ => return Err(MdocParseError::UnknownField(key_str.clone())),
        }
    }

    let slot0 = slots[0].ok_or(MdocParseError::MissingField("digestID"))?;
    let slot1 = slots[1].ok_or(MdocParseError::MissingField("random"))?;
    let slot2 = slots[2].ok_or(MdocParseError::MissingField("elementIdentifier"))?;
    let slot3 = slots[3].ok_or(MdocParseError::MissingField("elementValue"))?;

    let permutation = (slot3 << 6) | (slot2 << 4) | (slot1 << 2) | slot0;

    let mut offsets = [0usize; 4];
    // The bytes before the parsed map are the Tag 24 and byte-string headers;
    // the first key's offset additionally includes the map header itself.
    let prefix_len = cbor_issuer_signed_item
        .len()
        .checked_sub(inner_map.end)
        .ok_or(MdocParseError::ArithmeticOverflow(
            "IssuerSignedItem prefix length",
        ))?;
    offsets[0] =
        prefix_len
            .checked_add(pairs[0].0.start)
            .ok_or(MdocParseError::ArithmeticOverflow(
                "IssuerSignedItem first field offset",
            ))?;
    for i in 1..4 {
        offsets[i] =
            offsets[i - 1]
                .checked_add(length[i - 1])
                .ok_or(MdocParseError::ArithmeticOverflow(
                    "IssuerSignedItem field offset",
                ))?;
    }

    let digest_id_val = digest_id.ok_or(MdocParseError::MissingField("digestID"))?;

    let mso_digest_offset_in_preimage =
        required_digest_offset(value_digests, namespace, digest_id_val)?;

    Ok(ParsedAttr {
        name,
        cbor_value,
        cbor_issuer_signed_item: cbor_issuer_signed_item.to_vec(),
        mso_digest_offset_in_preimage,
        field_locator: FieldLocator {
            slot_position: offsets,
            length,
            permutation,
        },
    })
}

#[must_use]
pub fn compute_transcript_hash(transcript: &[u8], doc_type: &str) -> Vec<u8> {
    // Construct the DeviceAuthentication structure:
    // DeviceAuthentication = [
    //   "DeviceAuthentication",
    //   SessionTranscript,
    //   docType,
    //   deviceNameSpaces
    // ]
    let device_authentication_header = K_DEVICE_AUTHENTICATION_HEADER.to_vec();
    let mut doc_type_bytes = Vec::new();
    append_text_len(&mut doc_type_bytes, doc_type.len());
    doc_type_bytes.extend_from_slice(doc_type.as_bytes());

    let device_name_spaces_bytes = vec![0xD8, 0x18, 0x41, 0xA0]; // Tag 24 wrapping an empty map

    let mut device_authentication_cbor = device_authentication_header;
    device_authentication_cbor.extend_from_slice(transcript);
    device_authentication_cbor.extend_from_slice(&doc_type_bytes);
    device_authentication_cbor.extend_from_slice(&device_name_spaces_bytes);

    // Construct the COSE_Sign1 structure:
    // COSE_Sign1 = [
    //   protected,
    //   unprotected,
    //   payload,
    //   signature
    // ]
    let mut cose_sign1_bytes = K_COSE_SIGN1_SIGNING_HEADER.to_vec();

    let mut payload = K_TAG24.to_vec();
    append_bytes_len(&mut payload, device_authentication_cbor.len());
    payload.extend_from_slice(&device_authentication_cbor);

    append_bytes_len(&mut cose_sign1_bytes, payload.len());
    cose_sign1_bytes.extend_from_slice(&payload);

    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(&cose_sign1_bytes);
    hasher.finalize().to_vec()
}

fn format_cose_sign1_message(cbor_mso: &[u8]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(K_COSE_SIGN1_SIGNING_HEADER.len() + 3 + cbor_mso.len());
    buf.extend_from_slice(&K_COSE_SIGN1_SIGNING_HEADER);
    append_bytes_len(&mut buf, cbor_mso.len());
    buf.extend_from_slice(cbor_mso);
    buf
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::{
        compute_transcript_hash, parse_mdoc, parse_signature, required_map_value,
        validate_mso_layout, MdocParseError,
    };
    use crate::{
        compile::algebra::CompileNat,
        mdoc::circuits::cbor::{
            constants::{K_COSE_SIGN1_SIGNING_HEADER, K_DEVICE_AUTHENTICATION_HEADER},
            parse::CborParser,
        },
    };

    fn wrapped_mso(map_len: usize) -> (Vec<u8>, Vec<u8>) {
        let map = vec![0; map_len];
        let mut wrapped = vec![0xd8, 0x18, 0x59];
        wrapped.extend_from_slice(&(map_len as u16).to_be_bytes());
        wrapped.extend_from_slice(&map);
        (wrapped, map)
    }

    #[test]
    fn validates_fixed_mso_layout() {
        let (valid_wrapped, valid_map) = wrapped_mso(256);
        assert_eq!(validate_mso_layout(&valid_wrapped, &valid_map), Ok(()));

        let (short_wrapped, short_map) = wrapped_mso(255);
        assert_eq!(
            validate_mso_layout(&short_wrapped, &short_map),
            Err(MdocParseError::UnsupportedEncoding)
        );

        let (mut wrong_len_wrapped, wrong_len_map) = wrapped_mso(256);
        wrong_len_wrapped[4] = 1;
        assert_eq!(
            validate_mso_layout(&wrong_len_wrapped, &wrong_len_map),
            Err(MdocParseError::UnsupportedEncoding)
        );

        let (mut trailing_wrapped, trailing_map) = wrapped_mso(256);
        trailing_wrapped.push(0);
        assert_eq!(
            validate_mso_layout(&trailing_wrapped, &trailing_map),
            Err(MdocParseError::UnsupportedEncoding)
        );
    }

    #[test]
    fn rejects_mso_that_exceeds_sha_capacity() {
        let (wrapped, map) = wrapped_mso(2527);
        assert_eq!(
            validate_mso_layout(&wrapped, &map),
            Err(MdocParseError::TooBig)
        );
    }

    #[test]
    fn malformed_mdoc_returns_an_error() {
        assert!(matches!(
            parse_mdoc::<CompileNat<4>>(&[], &[], ""),
            Err(MdocParseError::Cbor {
                context: "root mdoc",
                ..
            })
        ));
    }

    #[test]
    fn nested_decoy_key_does_not_satisfy_schema() {
        let encoded = [
            0xa1, 0x65, b'o', b'u', b't', b'e', b'r', 0xa1, 0x69, b'd', b'o', b'c', b'u', b'm',
            b'e', b'n', b't', b's', 0x80,
        ];
        let mut parser = CborParser::new(&encoded);
        let root = parser.parse_exact().expect("test CBOR must be valid");

        assert!(matches!(
            required_map_value(&root, "documents", "root.documents"),
            Err(MdocParseError::MissingField("root.documents"))
        ));
    }

    #[test]
    fn duplicate_schema_key_is_rejected() {
        let encoded = [
            0xa2, 0x69, b'd', b'o', b'c', b'u', b'm', b'e', b'n', b't', b's', 0x80, 0x69, b'd',
            b'o', b'c', b'u', b'm', b'e', b'n', b't', b's', 0x80,
        ];
        let mut parser = CborParser::new(&encoded);
        let root = parser.parse_exact().expect("test CBOR must be valid");

        assert!(matches!(
            required_map_value(&root, "documents", "root.documents"),
            Err(MdocParseError::DuplicateField("root.documents"))
        ));
    }

    #[test]
    fn wrong_schema_container_type_is_rejected() {
        let encoded = [
            0xa1, 0x69, b'd', b'o', b'c', b'u', b'm', b'e', b'n', b't', b's', 0x00,
        ];
        assert!(matches!(
            parse_mdoc::<CompileNat<4>>(&encoded, &[], ""),
            Err(MdocParseError::UnexpectedType("root.documents"))
        ));
    }

    #[test]
    fn trailing_cbor_data_is_rejected() {
        assert!(matches!(
            parse_mdoc::<CompileNat<4>>(&[0xa0, 0x00], &[], ""),
            Err(MdocParseError::Cbor {
                context: "root mdoc",
                message,
            }) if message.starts_with("Trailing data after CBOR item")
        ));
    }

    #[test]
    fn malformed_signature_returns_an_error() {
        assert_eq!(
            parse_signature::<CompileNat<4>>(&[0; 63], "issuer signature"),
            Err(MdocParseError::InvalidLength {
                field: "issuer signature",
                expected: 64,
                actual: 63,
            })
        );
    }

    #[test]
    fn transcript_hash_uses_u32_lengths() {
        // An empty docType gives a fixed 27-byte overhead in DeviceAuthentication.
        let transcript = vec![0; 65_536 - 27];
        let actual = compute_transcript_hash(&transcript, "");

        let mut device_authentication = K_DEVICE_AUTHENTICATION_HEADER.to_vec();
        device_authentication.extend_from_slice(&transcript);
        device_authentication.push(0x60);
        device_authentication.extend_from_slice(&[0xd8, 0x18, 0x41, 0xa0]);
        assert_eq!(device_authentication.len(), 65_536);

        let mut expected_preimage = K_COSE_SIGN1_SIGNING_HEADER.to_vec();
        expected_preimage.extend_from_slice(&[0x5a, 0x00, 0x01, 0x00, 0x07]);
        expected_preimage.extend_from_slice(&[0xd8, 0x18, 0x5a, 0x00, 0x01, 0x00, 0x00]);
        expected_preimage.extend_from_slice(&device_authentication);
        let expected = Sha256::digest(&expected_preimage).to_vec();

        assert_eq!(actual, expected);
    }
    fn item_payload(digest: &[u8], random: &[u8]) -> Vec<u8> {
        let mut payload = b"\xa4\x68digestID".to_vec();
        payload.extend_from_slice(digest);
        payload.extend_from_slice(b"\x66random");
        payload.extend_from_slice(random);
        payload.extend_from_slice(b"\x71elementIdentifier\x64name\x6celementValue\xf5");
        payload
    }

    fn item_witness(
        payload: &[u8],
        wide_header: bool,
    ) -> Result<super::ParsedAttr, MdocParseError> {
        let mut wrapped = vec![0xd8, 0x18];
        if wide_header {
            wrapped.extend_from_slice(&[0x59, 0]);
        } else {
            wrapped.push(0x58);
        }
        wrapped.push(payload.len() as u8);
        wrapped.extend_from_slice(payload);
        let inner = CborParser::new(payload).parse_exact().unwrap();
        let mut digests = b"\xa1\x62ns\xa1\x01\x58\x20".to_vec();
        digests.extend_from_slice(&[0; 32]);
        let digests = CborParser::new(&digests).parse_exact().unwrap();
        super::compute_witness(
            b"name".to_vec(),
            vec![0xf5],
            &wrapped,
            &inner,
            &digests,
            "ns",
        )
    }

    #[test]
    fn item_witness_rejects_encodings_outside_the_circuit_layout() {
        for digest in [&[1][..], &[0x1a, 0, 0, 0, 1][..]] {
            let payload = item_payload(digest, &[0x41, 7]);
            let witness = item_witness(&payload, false).unwrap();
            assert_eq!(witness.field_locator.slot_position[0], 5);
            assert!(matches!(
                item_witness(&payload, true),
                Err(MdocParseError::UnsupportedEncoding)
            ));
        }
        let wide_id = item_payload(&[0x1b, 0, 0, 0, 0, 0, 0, 0, 1], &[0x41, 7]);
        assert!(matches!(
            item_witness(&wide_id, false),
            Err(MdocParseError::UnsupportedEncoding)
        ));
        for random in [&[0x61, b'r'][..], &[0][..]] {
            assert!(matches!(
                item_witness(&item_payload(&[1], random), false),
                Err(MdocParseError::UnexpectedType("IssuerSignedItem.random"))
            ));
        }
        assert!(item_witness(&item_payload(&[1], &[0x58, 1, 7]), false).is_ok());
        assert!(matches!(
            item_witness(&item_payload(&[1], &[0x59, 0, 1, 7]), false),
            Err(MdocParseError::UnsupportedEncoding)
        ));
        let mut wide_map = item_payload(&[1], &[0x41, 7]);
        wide_map.splice(0..1, [0xb8, 4]);
        assert!(matches!(
            item_witness(&wide_map, false),
            Err(MdocParseError::UnsupportedEncoding)
        ));
        let mut wide_key = item_payload(&[1], &[0x41, 7]);
        wide_key.splice(1..2, [0x78, 8]);
        assert!(matches!(
            item_witness(&wide_key, false),
            Err(MdocParseError::UnsupportedEncoding)
        ));
    }

    #[test]
    fn element_identifiers_are_unique_only_within_their_namespace() {
        let payload = item_payload(&[1], &[0x41, 7]);
        let mut item = vec![0xd8, 0x18, 0x58, payload.len() as u8];
        item.extend_from_slice(&payload);
        let mut digests = b"\xa2\x62ns\xa1\x01\x58\x20".to_vec();
        digests.extend_from_slice(&[0; 32]);
        digests.extend_from_slice(b"\x62ot\xa1\x01\x58\x20");
        digests.extend_from_slice(&[0; 32]);
        let digests = CborParser::new(&digests).parse_exact().unwrap();
        for same_namespace in [true, false] {
            let mut encoded = b"\xa1\x6anameSpaces".to_vec();
            encoded.extend_from_slice(if same_namespace {
                b"\xa1\x62ns\x82"
            } else {
                b"\xa2\x62ns\x81"
            });
            encoded.extend_from_slice(&item);
            if !same_namespace {
                encoded.extend_from_slice(b"\x62ot\x81");
            }
            encoded.extend_from_slice(&item);
            let issuer = CborParser::new(&encoded).parse_exact().unwrap();
            let result = super::extract_attrs(&issuer, &encoded, &digests);
            if same_namespace {
                assert!(matches!(
                    result,
                    Err(MdocParseError::DuplicateField(
                        "namespace elementIdentifier"
                    ))
                ));
            } else {
                let attributes = result.unwrap();
                assert_eq!(attributes.len(), 2);
                assert_eq!(attributes[0].name, attributes[1].name);
            }
        }
    }
}
