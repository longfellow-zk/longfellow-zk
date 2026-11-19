// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Fixed Merkle heap with leaves at `n..2*n` and parents below `n`.
//! Traversal and proof order also cover non-power-of-two leaf counts.
//! The v2 authentication codec binds each internal node to its heap position.

use std::fmt;

/// Returns a mask indicating which nodes in the heap lie on the path
/// from the requested leaves (`leaf_indices`) to the root.
pub(super) fn mark_paths_to_root(
    num_leaves: usize,
    leaf_indices: &[usize],
) -> Result<Vec<bool>, MerkleError> {
    if leaf_indices.is_empty() {
        return Err(MerkleError::EmptyLeaves);
    }
    let mut is_node_on_path = vec![false; 2 * num_leaves];
    for &leaf_idx in leaf_indices {
        if leaf_idx >= num_leaves {
            return Err(MerkleError::LeafIndexOutOfBounds {
                index: leaf_idx,
                num_leaves,
            });
        }
        let heap_idx = leaf_idx + num_leaves;
        if is_node_on_path[heap_idx] {
            return Err(MerkleError::DuplicateLeafIndex { index: leaf_idx });
        }
        is_node_on_path[heap_idx] = true;
    }
    // At least one leaf is marked, so its ancestors, the root among them,
    // are marked too.
    for i in (1..num_leaves).rev() {
        is_node_on_path[i] = is_node_on_path[2 * i] || is_node_on_path[2 * i + 1];
    }
    Ok(is_node_on_path)
}

/// The child of internal node `i` whose digest the frontier supplies, if
/// exactly one of its children is on a path (`is_node_on_path` from
/// `mark_paths_to_root`); `i` itself is then on a path.
pub(super) fn frontier_child(is_node_on_path: &[bool], i: usize) -> Option<usize> {
    let (left, right) = (is_node_on_path[2 * i], is_node_on_path[2 * i + 1]);
    // The off-path child: the right one when the left is on a path.
    (left != right).then_some(2 * i + usize::from(left))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::runtime::v2) enum MerkleError {
    DuplicateLeafIndex { index: usize },
    LeafIndexOutOfBounds { index: usize, num_leaves: usize },
    EmptyLeaves,
}

impl fmt::Display for MerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateLeafIndex { index } => {
                write!(f, "duplicate leaf index requested: {index}")
            }
            Self::LeafIndexOutOfBounds { index, num_leaves } => write!(
                f,
                "leaf index {index} out of bounds (tree has {num_leaves} leaves)"
            ),
            Self::EmptyLeaves => {
                write!(f, "empty leaves requested for verification")
            }
        }
    }
}

impl std::error::Error for MerkleError {}
