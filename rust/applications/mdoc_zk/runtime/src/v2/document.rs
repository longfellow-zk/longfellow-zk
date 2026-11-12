// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 host validation on original CBOR values, before lossy conversions.
//! These checks give early errors; the circuit remains the acceptance rule.
use super::inputs::timestamp_digits;
use crate::{
    core::algebra::{AlgebraicField, Curve, SerializableField},
    mdoc::circuits::cbor::{
        mdoc::{map_entry_unique, parse_mdoc_with_mso_check, MdocParseError, ParsedMdoc},
        parse::{CborElement, CborValue},
    },
    runtime::algebra::{p256::P256Field, secp256r1::Secp256r1, RuntimeNat},
};

#[derive(Debug)]
pub(super) enum Error {
    Encoding(MdocParseError),
    Predicate,
}
impl From<MdocParseError> for Error {
    fn from(value: MdocParseError) -> Self {
        Self::Encoding(value)
    }
}

pub(super) fn parse(
    bytes: &[u8],
    transcript: &[u8],
    doc_type: &str,
    now: &str,
    field: &P256Field,
) -> Result<ParsedMdoc<RuntimeNat<4>>, Error> {
    parse_mdoc_with_mso_check(bytes, transcript, doc_type, |mso| {
        validate_mso(mso, doc_type, now, field)
    })
}

fn text_entry<'a>(
    map: &'a CborElement,
    name: &str,
    path: &'static str,
) -> Result<&'a CborElement, MdocParseError> {
    Ok(map_entry_unique(map, name, path)?.1)
}
fn integer_entry(map: &CborElement, key: i128) -> Result<&CborElement, MdocParseError> {
    let CborValue::Map(pairs) = &map.value else {
        return Err(MdocParseError::UnexpectedType(
            "MSO.deviceKeyInfo.deviceKey",
        ));
    };
    let mut matching = pairs
        .iter()
        .filter(|(k, _)| matches!(k.value, CborValue::Integer(n) if n == key));
    let value = matching
        .next()
        .ok_or(MdocParseError::MissingField("device key parameter"))?;
    if matching.next().is_some() {
        return Err(MdocParseError::DuplicateField("device key parameter"));
    }
    Ok(&value.1)
}
fn coordinate(
    key: &CborElement,
    index: i128,
    field: &P256Field,
) -> Result<crate::runtime::algebra::p256::P256Element, MdocParseError> {
    let CborValue::Bytes(bytes) = &integer_entry(key, index)?.value else {
        return Err(MdocParseError::UnexpectedType("device coordinate"));
    };
    let mut canonical: [u8; 32] =
        bytes
            .as_slice()
            .try_into()
            .map_err(|_| MdocParseError::InvalidLength {
                field: "device coordinate",
                expected: 32,
                actual: bytes.len(),
            })?;
    canonical.reverse();
    field
        .bytes_to_element(&canonical)
        .map_err(|_| MdocParseError::InvalidValue("noncanonical device coordinate"))
}
fn timestamp(value: &CborElement) -> Result<[u8; 14], MdocParseError> {
    let CborValue::Tag(0, inner) = &value.value else {
        return Err(MdocParseError::UnexpectedType("validity timestamp"));
    };
    let CborValue::Text(text) = &inner.value else {
        return Err(MdocParseError::UnexpectedType("validity timestamp"));
    };
    timestamp_digits(text.as_bytes()).ok_or(MdocParseError::InvalidValue("validity timestamp"))
}
fn validate_mso(
    mso: &CborElement,
    doc_type: &str,
    now: &str,
    field: &P256Field,
) -> Result<(), Error> {
    let CborValue::Text(actual_doc_type) = &text_entry(mso, "docType", "MSO.docType")?.value else {
        return Err(MdocParseError::UnexpectedType("MSO.docType").into());
    };
    if actual_doc_type != doc_type {
        return Err(Error::Predicate);
    }
    let validity = text_entry(mso, "validityInfo", "MSO.validityInfo")?;
    let from = timestamp(text_entry(
        validity,
        "validFrom",
        "MSO.validityInfo.validFrom",
    )?)?;
    let until = timestamp(text_entry(
        validity,
        "validUntil",
        "MSO.validityInfo.validUntil",
    )?)?;
    let current = timestamp_digits(now.as_bytes()).ok_or(Error::Predicate)?;
    if !(from <= current && current <= until) {
        return Err(Error::Predicate);
    }
    let info = text_entry(mso, "deviceKeyInfo", "MSO.deviceKeyInfo")?;
    let key = text_entry(info, "deviceKey", "MSO.deviceKeyInfo.deviceKey")?;
    if !matches!(integer_entry(key, 1)?.value, CborValue::Integer(2))
        || !matches!(integer_entry(key, -1)?.value, CborValue::Integer(1))
    {
        return Err(Error::Predicate);
    }
    let x = coordinate(key, -2, field)?;
    let y = coordinate(key, -3, field)?;
    let curve = Secp256r1::new(field);
    let rhs = field.addf(
        &field.mulf(&field.addf(&field.mulf(&x, &x), curve.a()), &x),
        curve.b(),
    );
    if field.mulf(&y, &y) != rhs {
        return Err(Error::Predicate);
    }
    Ok(())
}

#[cfg(test)]
#[path = "../../tests/v2_document.rs"]
mod tests;
