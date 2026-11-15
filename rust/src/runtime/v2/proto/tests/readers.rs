// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::{
    sumcheck::{SumcheckProof, SumcheckProofGeometry},
    MerkleProof,
};
use crate::core::algebra::{BareField, FieldID, SerializableField};

#[test]
fn merkle_frontier_is_its_count_of_digests_within_the_checked_path_bound() {
    let mut frontier = 3u64.to_le_bytes().to_vec();
    frontier.extend([7u8; 96]);
    frontier.push(9);
    let mut rest = &frontier[..];
    assert_eq!(MerkleProof::read_path(&mut rest, 3, 1).unwrap().len(), 3);
    // The count says where the frontier ends; the caller checks what follows.
    assert_eq!(rest, [9]);
    assert!(MerkleProof::read_path(&mut &frontier[..], 2, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..103], 3, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..7], 3, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..], usize::MAX, 2).is_err());
}

struct ZeroWidth;
impl BareField for ZeroWidth {
    type E = u64;
}
impl SerializableField for ZeroWidth {
    fn field_id(&self) -> FieldID {
        FieldID::None
    }
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        0
    }
    fn to_bytes_into(&self, _: &u64, _: &mut [u8]) {}
    fn bytes_to_element(&self, _: &[u8]) -> Result<u64, String> {
        Ok(0)
    }
    fn serialized_mone(&self) -> Vec<u8> {
        Vec::new()
    }
}
#[test]
fn sumcheck_rejects_a_zero_width_codec_before_decoding() {
    let geometry = SumcheckProofGeometry::new(vec![]);
    assert!(SumcheckProof::<2, ZeroWidth>::read(&mut &[][..], &geometry, &ZeroWidth).is_err());
}
