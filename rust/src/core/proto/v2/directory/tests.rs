// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use std::mem::size_of;

use super::*;
use crate::core::proto::v2::Layer;

/// The fixed charges cover what the reader holds in memory on this target.
#[test]
fn metadata_charges_cover_the_host_layout() {
    assert!(
        2 * size_of::<u32>() + 9 * size_of::<i64>() + size_of::<usize>() <= SEGMENT_METADATA_BYTES
    );
    assert!(size_of::<u32>() <= TOKEN_METADATA_BYTES);
    assert!(size_of::<LayerDirectory>() + size_of::<Layer>() <= LAYER_METADATA_BYTES);
}

/// The metadata limit admits the same segment count on every target.
#[test]
fn metadata_limit_does_not_depend_on_the_target() {
    let max = (MAX_METADATA_BYTES - LAYER_METADATA_BYTES) / SEGMENT_METADATA_BYTES;
    let check = |segments| {
        let mut streams = [StreamDirectory::default(); 3];
        streams[0].segments = segments;
        validate(&[LayerDirectory { nw: 1, streams }], 1, 1, 0, 0, 0)
    };
    assert!(check(max).is_ok());
    assert!(check(max + 1)
        .unwrap_err()
        .contains("segment/token metadata"));
}
