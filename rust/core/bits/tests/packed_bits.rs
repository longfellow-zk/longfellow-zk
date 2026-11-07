// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::PackedBits;
#[test]
fn logical_coordinates_cross_word_boundaries_and_pad_only_the_final_word() {
    for len in [0, 1, 7, 8, 63, 64, 65, 127, 128, 129, 255, 256, 257] {
        let values: Vec<_> = (0..len).map(|i| i % 3 == 1).collect();
        let bits: PackedBits = values.iter().copied().collect();
        assert_eq!(bits.len(), len);
        for (i, &value) in values.iter().enumerate() {
            assert_eq!(bits.get(i), value);
        }
        for block in 0..len.div_ceil(128) + 1 {
            let expected = (0..128).fold(0, |word, i| {
                word | (u128::from(values.get(block * 128 + i).copied().unwrap_or(false)) << i)
            });
            assert_eq!(bits.word128(block), expected);
        }
        assert!(bits.slice(len..len + 1).is_err());
        assert!(bits.slice(std::ops::Range { start: 1, end: 0 }).is_err());
    }
}
#[test]
fn byte_import_rejects_wrong_lengths_and_noncanonical_padding() {
    assert!(PackedBits::from_le_bytes(&[], 1).is_err());
    assert!(PackedBits::from_le_bytes(&[0], 0).is_err());
    assert!(PackedBits::from_le_bytes(&[0x80], 7).is_err());
    let bits = PackedBits::from_le_bytes(&[0xa5, 1], 9).unwrap();
    assert_eq!(bits.word128(0), 0x1a5);
    assert_eq!(bits.slice(6..9).unwrap().word128(0), 6);
    assert_eq!(bits.word128(usize::MAX), 0);
}
