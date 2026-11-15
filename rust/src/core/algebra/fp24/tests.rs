// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{BASE_SERIALIZED_SIZE, EXTENSION_DEGREE, Q, SERIALIZED_SIZE};
use crate::core::algebra::{encoding::FP24_EXT6, SerializableField};
#[test]
fn sextic_encoding_checks_each_coordinate_and_exact_width() {
    assert_eq!(BASE_SERIALIZED_SIZE * EXTENSION_DEGREE, SERIALIZED_SIZE);
    let canonical =
        std::array::from_fn::<_, SERIALIZED_SIZE, _>(
            |i| if i % 3 == 0 { (i / 3) as u8 } else { 0 },
        );
    assert_eq!(FP24_EXT6.bytes_to_element(&canonical).unwrap(), canonical);
    assert_eq!(FP24_EXT6.serialized_mone()[..3], (Q - 1).to_le_bytes()[..3]);
    assert!(FP24_EXT6
        .bytes_to_element(&canonical[..SERIALIZED_SIZE - 1])
        .is_err());
    let mut too_long = canonical.to_vec();
    too_long.push(0);
    assert!(FP24_EXT6.bytes_to_element(&too_long).is_err());
    for coordinate in 0..EXTENSION_DEGREE {
        let mut invalid = canonical;
        invalid[3 * coordinate..3 * coordinate + 3].copy_from_slice(&Q.to_le_bytes()[..3]);
        assert!(FP24_EXT6.bytes_to_element(&invalid).is_err());
    }
}
