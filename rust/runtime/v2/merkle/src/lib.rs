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

pub(in crate::runtime::v2) mod hash;
mod heap;

use std::fmt;

#[cfg(any(test, feature = "verifier"))]
pub(in crate::runtime::v2) use heap::verify_proof_with_hash;
#[cfg(any(test, feature = "prover"))]
pub(in crate::runtime::v2) use heap::MerkleHeap;

use crate::runtime::v2::proto::Digest;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::runtime::v2) enum MerkleError {
    DuplicateLeafIndex {
        index: usize,
    },
    LeafIndexOutOfBounds {
        index: usize,
        num_leaves: usize,
    },
    #[cfg(any(test, feature = "verifier"))]
    ProofLengthMismatch {
        expected: usize,
        found: usize,
    },
    #[cfg(any(test, feature = "verifier"))]
    RootMismatch {
        expected: Digest,
        found: Digest,
    },
    EmptyLeaves,
    LeafIndexNotOnPath,
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
            #[cfg(any(test, feature = "verifier"))]
            Self::ProofLengthMismatch { expected, found } => write!(
                f,
                "proof length mismatch: expected {expected}, found {found}"
            ),
            #[cfg(any(test, feature = "verifier"))]
            Self::RootMismatch { expected, found } => write!(
                f,
                "root mismatch: expected root {:?}, computed root {:?}",
                expected.data, found.data
            ),
            Self::EmptyLeaves => {
                write!(f, "empty leaves requested for verification")
            }
            Self::LeafIndexNotOnPath => {
                write!(f, "leaf index is not on the path to the root")
            }
        }
    }
}

impl std::error::Error for MerkleError {}
