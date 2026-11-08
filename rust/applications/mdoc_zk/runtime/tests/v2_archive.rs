// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn compressed_file_reads_stop_at_the_named_limit() {
    let input = std::io::repeat(0).take((MAX_ARCHIVE_BYTES + 100) as u64);
    assert!(read_compressed(input).is_err());
    assert_eq!(
        read_compressed(std::io::repeat(0).take(MAX_ARCHIVE_BYTES as u64))
            .unwrap()
            .len(),
        MAX_ARCHIVE_BYTES
    );
    assert!(read(&vec![0; MAX_ARCHIVE_BYTES + 1]).is_err());
}
#[test]
fn compressed_archive_checks_trailing_data_and_window_size() {
    let mut builder = CircuitArchive::builder();
    builder.set_circuit_version(12);
    let archive = builder.build().to_bytes();
    let compressed = zstd::encode_all(archive.as_slice(), 19).unwrap();
    assert!(read(&compressed).is_ok());
    let mut trailing = archive;
    trailing.push(0);
    assert!(read(&zstd::encode_all(trailing.as_slice(), 19).unwrap())
        .unwrap_err()
        .contains("Trailing"));
    // Streaming zstd frames declare their window separately from the payload.
    // Requesting a larger window must fail before parsing archive contents.
    assert_eq!(compressed[4] & 0x20, 0);
    let mut large_window = compressed;
    large_window[5] = ((MAX_METADATA_BYTES.ilog2() + 1 - 10) * 8) as u8;
    assert!(read(&large_window).unwrap_err().contains("memory"));
}
