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

//! Canonical salted column and Merkle node hashes shared by both roles.
//!
//! The Merkle module owns tree construction and path verification. These two
//! hash functions supply Polygero's context and distinct leaf/node tags. A leaf
//! binds its column index, salt and every W row in order. Hashing always uses
//! canonical full-width field bytes.
use sha2::{Digest as _, Sha256};

use crate::{
    core::algebra::SerializableField,
    runtime::proto::{Digest, MerkleNonce},
};

/// Hash one internal node with the protocol context and a node-specific tag.
pub(super) fn node(context: &Digest, left: &Digest, right: &Digest) -> Digest {
    let mut hash = Sha256::new();
    hash.update(b"polygero/root/node/v1");
    hash.update(context.data);
    hash.update(left.data);
    hash.update(right.data);
    Digest {
        data: hash.finalize().into(),
    }
}
/// Canonically hash a salted original column in row order.
pub(super) fn leaf<'a, F: SerializableField>(
    context: &Digest,
    index: usize,
    column: impl IntoIterator<Item = &'a F::E>,
    salt: &MerkleNonce,
    f: &F,
) -> Digest
where
    F::E: 'a,
{
    let mut hash = Sha256::new();
    hash.update(b"polygero/root/original-leaf/v1");
    hash.update(context.data);
    hash.update((index as u64).to_le_bytes());
    hash.update(salt.bytes);
    // Reuse the canonical field buffer across a column. Allocating once per
    // cell otherwise creates millions of small allocations during commitment.
    let mut encoded = vec![0; f.serialized_size_bytes()];
    for value in column {
        f.to_bytes_into(value, &mut encoded);
        hash.update(&encoded);
    }
    Digest {
        data: hash.finalize().into(),
    }
}
