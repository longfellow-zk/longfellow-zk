// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! A parsed mdoc and the errors of parsing one.

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

impl<N> ParsedMdoc<N> {
    pub fn all_attr_ids(&self) -> Vec<&[u8]> {
        self.attrs.iter().map(|a| a.name.as_slice()).collect()
    }

    pub fn get_attribute(&self, name: &[u8]) -> Option<&ParsedAttr> {
        self.attrs.iter().find(|a| a.name == name)
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
