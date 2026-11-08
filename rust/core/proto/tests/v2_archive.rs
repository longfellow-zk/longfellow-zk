// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core::proto::{archive::CircuitArchiveBuilder, serialize_uleb128_max4};

fn prefix(entries: usize) -> Vec<u8> {
    let mut out = b"LFA2".to_vec();
    out.push(LFA_VERSION);
    serialize_uleb128_max4(&mut out, 12);
    out.extend([0; 32]);
    out.extend([0; 4]);
    serialize_uleb128_max4(&mut out, entries);
    out
}
fn entry(out: &mut Vec<u8>, name: &str, size: usize) {
    serialize_uleb128_max4(out, name.len());
    out.extend(name.as_bytes());
    out.extend([0; 32]);
    serialize_uleb128_max4(out, size);
}
#[test]
fn archive_roundtrip_handles_small_input_buffers() {
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(12);
    builder.add_entry("sig", [1; 32], vec![1, 2, 3]);
    builder.add_entry("hash", [2; 32], vec![4, 5]);
    let expected = builder.build();
    let bytes = expected.to_bytes();
    let mut stream = std::io::BufReader::with_capacity(1, bytes.as_slice());
    assert_eq!(from_stream(&mut stream).unwrap(), expected);
    assert_eq!(from_bytes(&bytes).unwrap(), expected);
    for n in 0..bytes.len() {
        assert!(from_bytes(&bytes[..n]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(from_bytes(&trailing).is_err());
}
#[test]
fn archive_rejects_large_lengths_in_the_directory() {
    let mut bytes = prefix(1);
    entry(&mut bytes, "sig", MAX_ARCHIVE_BYTES + 1);
    assert!(from_bytes(&bytes).unwrap_err().contains("payload length"));
    let mut oversized_total = prefix(2);
    entry(&mut oversized_total, "sig", MAX_ARCHIVE_BYTES / 2 + 1);
    entry(&mut oversized_total, "hash", MAX_ARCHIVE_BYTES / 2 + 1);
    assert!(from_bytes(&oversized_total)
        .unwrap_err()
        .contains("total payload"));
    assert!(from_bytes(&prefix(MAX_ARCHIVE_ENTRIES + 1))
        .unwrap_err()
        .contains("entry count"));
    let mut duplicate = prefix(2);
    entry(&mut duplicate, "sig", 0);
    entry(&mut duplicate, "sig", 0);
    assert!(from_bytes(&duplicate).unwrap_err().contains("Duplicate"));
}
#[test]
fn archive_size_decoding_rejects_unrepresentable_values() {
    for value in [
        &[0xff, 0xff, 0xff, 0xff, 0x7f][..],
        &[0x80, 0x80, 0x80, 0x80, 0x80, 1][..],
    ] {
        let mut bytes = b"LFA2".to_vec();
        bytes.push(LFA_VERSION);
        bytes.extend(value);
        assert!(from_bytes(&bytes).is_err());
    }
}
#[test]
fn archive_metadata_has_one_aggregate_limit() {
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(12);
    builder.set_created_at("");
    builder.set_author("");
    builder.set_generator_tool("");
    builder.set_description("x".repeat(MAX_METADATA_BYTES));
    assert!(from_bytes(&builder.clone().build().to_bytes()).is_ok());
    builder.set_author("x");
    assert!(from_bytes(&builder.build().to_bytes())
        .unwrap_err()
        .contains("metadata"));
}
