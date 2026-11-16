// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's check of an opening against the root.
use std::fmt;

use super::{
    hash,
    heap::{mark_paths_to_root, MerkleError},
};
use crate::runtime::v2::proto::Digest;

/// Verifies that the opened leaf digests match the commitment root.
///
/// Geometry fixes every leaf position. Opened indices must be distinct and
/// in range, and the supplied frontier must be consumed exactly. Each internal
/// node is hashed once, with its position supplied by this traversal.
pub(in crate::runtime::v2) fn verify_proof(
    num_leaves: usize,
    root: &Digest,
    proof: &[Digest],
    leaves: &[(usize, Digest)],
) -> Result<(), OpeningError> {
    let leaf_indices: Vec<usize> = leaves.iter().map(|(idx, _)| *idx).collect();
    // `None` means this node has not been supplied or derived.  Do not use a
    // sentinel digest here: an all-zero digest is valid proof data and must
    // never be confused with an uncomputed node.
    let mut computed_nodes = vec![None; 2 * num_leaves];

    let is_node_on_path = mark_paths_to_root(num_leaves, &leaf_indices)?;
    let mut proof_idx = 0;

    // 1. Populate sibling nodes from the proof path
    for i in (1..num_leaves).rev() {
        if is_node_on_path[i] {
            if is_node_on_path[2 * i] && !is_node_on_path[2 * i + 1] {
                if proof_idx >= proof.len() {
                    return Err(OpeningError::ProofLengthMismatch {
                        expected: proof_idx + 1,
                        found: proof.len(),
                    });
                }
                computed_nodes[2 * i + 1] = Some(proof[proof_idx]);
                proof_idx += 1;
            } else if !is_node_on_path[2 * i] && is_node_on_path[2 * i + 1] {
                if proof_idx >= proof.len() {
                    return Err(OpeningError::ProofLengthMismatch {
                        expected: proof_idx + 1,
                        found: proof.len(),
                    });
                }
                computed_nodes[2 * i] = Some(proof[proof_idx]);
                proof_idx += 1;
            }
        }
    }

    // A valid multi-proof has exactly the sibling nodes requested by the
    // traversal.  Reject trailing entries rather than silently accepting a
    // second encoding of the same opening.
    if proof_idx != proof.len() {
        return Err(OpeningError::ProofLengthMismatch {
            expected: proof_idx,
            found: proof.len(),
        });
    }

    // 2. Populate the opened leaves
    for &(leaf_idx, leaf_digest) in leaves {
        let heap_idx = leaf_idx + num_leaves;
        computed_nodes[heap_idx] = Some(leaf_digest);
    }

    // 3. Reconstruct internal nodes bottom-up
    for i in (1..num_leaves).rev() {
        if let (Some(left), Some(right)) = (computed_nodes[2 * i], computed_nodes[2 * i + 1]) {
            computed_nodes[i] = Some(hash::node(i, &left, &right));
        }
    }

    let computed_root = computed_nodes[1].ok_or(OpeningError::RootMismatch {
        expected: *root,
        found: Digest::default(),
    })?;
    if root != &computed_root {
        return Err(OpeningError::RootMismatch {
            expected: *root,
            found: computed_root,
        });
    }
    Ok(())
}

/// Why an opening fails: its leaf positions do not form paths of the heap,
/// or its frontier does not rebuild the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::runtime::v2) enum OpeningError {
    Paths(MerkleError),
    ProofLengthMismatch { expected: usize, found: usize },
    RootMismatch { expected: Digest, found: Digest },
}

impl From<MerkleError> for OpeningError {
    fn from(error: MerkleError) -> Self {
        Self::Paths(error)
    }
}

impl fmt::Display for OpeningError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Paths(error) => error.fmt(f),
            Self::ProofLengthMismatch { expected, found } => write!(
                f,
                "proof length mismatch: expected {expected}, found {found}"
            ),
            Self::RootMismatch { expected, found } => write!(
                f,
                "root mismatch: expected root {:?}, computed root {:?}",
                expected.data, found.data
            ),
        }
    }
}

impl std::error::Error for OpeningError {}
