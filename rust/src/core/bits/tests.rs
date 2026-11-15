// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::PackedBits;
#[test]
fn logical_coordinates_cross_word_boundaries_and_pad_only_the_final_word() {
    for len in [0usize, 1, 7, 8, 63, 64, 65, 127, 128, 129, 255, 256, 257] {
        let values: Vec<_> = (0..len).map(|i| i % 3 == 1).collect();
        let bits: PackedBits = values.iter().copied().collect();
        for block in 0..len.div_ceil(128) + 1 {
            let expected = (0..128).fold(0, |word, i| {
                word | (u128::from(values.get(block * 128 + i).copied().unwrap_or(false)) << i)
            });
            assert_eq!(bits.word128(block), expected);
        }
    }
    let bits: PackedBits = [true; 9].into_iter().collect();
    assert_eq!(bits.word128(usize::MAX), 0);
}
