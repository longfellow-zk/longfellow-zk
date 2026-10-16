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

use core_algebra::{Nat, SerializableField};
use runtime_algebra::p256::P256Field;

use crate::attribute::{AttributeOp, RequestedAttribute};

pub fn req_attr(
    namespace: impl AsRef<[u8]>,
    id: impl AsRef<[u8]>,
    cbor_val: impl AsRef<[u8]>,
) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: id.as_ref().to_vec(),
        cbor_value: cbor_val.as_ref().to_vec(),
        op: AttributeOp::Eq,
        context: Vec::new(),
    }
}

pub fn req_attr_le(
    namespace: impl AsRef<[u8]>,
    id: impl AsRef<[u8]>,
    cbor_val: impl AsRef<[u8]>,
) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: id.as_ref().to_vec(),
        cbor_value: cbor_val.as_ref().to_vec(),
        op: AttributeOp::Le,
        context: Vec::new(),
    }
}

pub fn req_attr_ge(
    namespace: impl AsRef<[u8]>,
    id: impl AsRef<[u8]>,
    cbor_val: impl AsRef<[u8]>,
) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: id.as_ref().to_vec(),
        cbor_value: cbor_val.as_ref().to_vec(),
        op: AttributeOp::Ge,
        context: Vec::new(),
    }
}

pub fn req_pnym(namespace: impl AsRef<[u8]>, context: impl AsRef<[u8]>) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: b"pnym_seed".to_vec(),
        cbor_value: Vec::new(),
        op: AttributeOp::Pnym,
        context: context.as_ref().to_vec(),
    }
}

#[must_use]
pub fn pad_request_attrs(
    attrs: &[RequestedAttribute],
    target_len: usize,
) -> Vec<RequestedAttribute> {
    if attrs.is_empty()
        || attrs.len() >= target_len
        || attrs.iter().any(|a| a.op == AttributeOp::Pnym)
    {
        return attrs.to_vec();
    }
    let mut out = attrs.to_vec();
    let last = attrs.last().unwrap().clone();
    while out.len() < target_len {
        out.push(last.clone());
    }
    out
}

#[must_use]
pub fn same_namespace(attrs: &[RequestedAttribute]) -> bool {
    if attrs.is_empty() {
        return true;
    }
    let ns = &attrs[0].namespace_id;
    attrs.iter().all(|a| a.namespace_id == *ns)
}

fn hex_decode_to_32_bytes_be(s: &str) -> Result<[u8; 32], String> {
    let mut bytes = [0u8; 32];
    let hex_len = s.len();
    if hex_len == 0 || hex_len > 64 {
        return Err("Invalid hex string length".to_string());
    }

    let mut s_padded = s.to_string();
    if hex_len < 64 {
        s_padded = format!("{s:0>64}");
    }

    for (i, byte) in bytes.iter_mut().enumerate() {
        let high = char_to_digit(s_padded.as_bytes()[2 * i])?;
        let low = char_to_digit(s_padded.as_bytes()[2 * i + 1])?;
        *byte = (high << 4) | low;
    }
    Ok(bytes)
}

fn char_to_digit(c: u8) -> Result<u8, String> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        _ => Err(format!("Invalid hex character: {}", char::from(c))),
    }
}

pub fn parse_hex_nat<const W: usize, N: Nat<W>>(s: &str) -> Result<N, String> {
    let s_clean = s.strip_prefix("0x").unwrap_or(s);
    let mut bytes_be = hex_decode_to_32_bytes_be(s_clean)?;
    bytes_be.reverse();
    Ok(N::from_bytes_le(&bytes_be))
}

pub fn parse_pk_coordinate(
    s: &str,
    field: &P256Field,
) -> Result<runtime_algebra::p256::P256Element, String> {
    let nat = parse_hex_nat::<4, runtime_algebra::RuntimeNat<4>>(s)?;
    field.bytes_to_element(&nat.to_bytes_le())
}

#[must_use]
pub fn is_iso_date_prefix(bytes: &[u8]) -> bool {
    bytes.len() >= 10
        && bytes[0..4].iter().all(u8::is_ascii_digit)
        && bytes[4] == b'-'
        && bytes[5..7].iter().all(u8::is_ascii_digit)
        && bytes[7] == b'-'
        && bytes[8..10].iter().all(u8::is_ascii_digit)
}

#[must_use]
pub fn is_iso_datetime_utc(bytes: &[u8]) -> bool {
    is_iso_date_prefix(bytes)
        && bytes.len() == mdoc_zk_proto::hash::constants::K_TIMESTAMP_LEN
        && bytes[10] == b'T'
        && bytes[11..13].iter().all(u8::is_ascii_digit)
        && bytes[13] == b':'
        && bytes[14..16].iter().all(u8::is_ascii_digit)
        && bytes[16] == b':'
        && bytes[17..19].iter().all(u8::is_ascii_digit)
        && bytes[19] == b'Z'
}

/// Checks whether an attribute with identifier `id` and CBOR-encoded value
/// `cbor_value` can fit inside the circuit's disclosed attribute buffers
/// (`cbor_id.len() <= 32`, `cbor_value.len() <= 64`) and within an
/// `IssuerSignedItemBytes` hashed by `num_attr_sha_blocks` SHA-256 blocks
/// (`min_attr_item_cbor_len <= max_attr_cbor_len(num_attr_sha_blocks)`).
#[must_use]
pub fn attr_encoding_fits(id: &[u8], cbor_value: &[u8], num_attr_sha_blocks: usize) -> bool {
    if id.is_empty() || cbor_value.is_empty() || cbor_value.len() > 64 {
        return false;
    }
    let cbor_id_len = if id.len() < 24 {
        1 + id.len()
    } else {
        2 + id.len()
    };
    if cbor_id_len > 32 {
        return false;
    }
    mdoc_zk_proto::mso_attribute::constants::min_attr_item_cbor_len(cbor_id_len, cbor_value.len())
        <= mdoc_zk_proto::mso_attribute::constants::max_attr_cbor_len(num_attr_sha_blocks)
}

/// Binds a prover-returned attribute response slice against the verifier's own
/// requested attributes.
///
/// For `AttributeOp::Pnym` entries, copies only the prover-computed 34-byte CBOR
/// pseudonym (`0x58 0x20 || H(pnym_seed || context)`) into a copy of the
/// verifier's `request`, keeping all verifier-chosen fields (`namespace_id`,
/// `id`, `op`, `context`) and all non-`Pnym` attributes strictly from `request`.
pub fn bind_pnym_response(
    request: &[RequestedAttribute],
    response: &[RequestedAttribute],
) -> Result<Vec<RequestedAttribute>, crate::error::MdocVerifierErrorCode> {
    if request.len() != response.len() {
        return Err(crate::error::MdocVerifierErrorCode::AttributeNumberMismatch);
    }
    let mut bound = request.to_vec();
    for (req, resp) in bound.iter_mut().zip(response.iter()) {
        if req.namespace_id != resp.namespace_id || req.id != resp.id || req.op != resp.op {
            return Err(crate::error::MdocVerifierErrorCode::InvalidRequest);
        }
        if req.op == AttributeOp::Pnym {
            if resp.cbor_value.len() != mdoc_zk_proto::mso_attribute::constants::K_PNYM_VALUE_LEN
                || resp.cbor_value.get(..2) != Some(&[0x58, 0x20])
            {
                return Err(crate::error::MdocVerifierErrorCode::InvalidRequest);
            }
            req.cbor_value = resp.cbor_value.clone();
        } else if req.cbor_value != resp.cbor_value || !resp.context.is_empty() {
            return Err(crate::error::MdocVerifierErrorCode::InvalidRequest);
        }
    }
    Ok(bound)
}

#[must_use]
pub fn circuit_supports(data: &[u8]) -> bool {
    let mut parser = mdoc_zk_circuits::cbor::parse::CborParser::new(data);
    let Ok(el) = parser.parse_exact() else {
        return false;
    };
    match &el.value {
        mdoc_zk_circuits::cbor::parse::CborValue::Text(_)
        | mdoc_zk_circuits::cbor::parse::CborValue::Bytes(_)
        | mdoc_zk_circuits::cbor::parse::CborValue::Integer(_) => true,
        mdoc_zk_circuits::cbor::parse::CborValue::Simple(info) => *info == 20 || *info == 21,
        mdoc_zk_circuits::cbor::parse::CborValue::Tag(tag, inner) => match tag {
            1004 => {
                if data.len() != 14 {
                    return false;
                }
                matches!(
                    inner.value,
                    mdoc_zk_circuits::cbor::parse::CborValue::Text(_)
                )
            }
            0 => {
                if data.len() != 22 {
                    return false;
                }
                matches!(
                    inner.value,
                    mdoc_zk_circuits::cbor::parse::CborValue::Text(_)
                )
            }
            _ => false,
        },
        _ => false,
    }
}

#[must_use]
pub fn circuit_supports_comparison(data: &[u8]) -> bool {
    if !circuit_supports(data) {
        return false;
    }
    if data.len() == 14 && data.starts_with(&[0xd9, 0x03, 0xec, 0x6a]) {
        is_iso_date_prefix(&data[4..14])
    } else if data.len() == 22 && data.starts_with(&[0xc0, 0x74]) {
        is_iso_datetime_utc(&data[2..22])
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::circuit_supports;

    #[test]
    fn circuit_supports_rejects_malformed_trailing_data() {
        assert!(!circuit_supports(&[0x01, 0xff]));
    }
}
