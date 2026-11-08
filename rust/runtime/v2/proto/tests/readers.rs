// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    sumcheck::{SumcheckProof, SumcheckProofGeometry},
    MerkleProof,
};
use crate::core::algebra::{BareField, SerializableField};

#[test]
fn merkle_frontier_checks_available_bytes_and_checked_path_bound() {
    let prefix = 100_000u32.to_le_bytes();
    let error = MerkleProof::read_path(&mut prefix.as_slice(), 100_000, 1).unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::UnexpectedEof);
    assert!(MerkleProof::read_path(&mut prefix.as_slice(), usize::MAX, 2).is_err());
}

struct ZeroWidth;
impl BareField for ZeroWidth {
    type E = u64;
}
impl SerializableField for ZeroWidth {
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
