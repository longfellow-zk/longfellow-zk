// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The hash of the device authentication over a session transcript.
use crate::mdoc::cbor::{
    append_bytes_len, append_text_len,
    constants::{K_COSE_SIGN1_SIGNING_HEADER, K_DEVICE_AUTHENTICATION_HEADER, K_TAG24},
};

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
