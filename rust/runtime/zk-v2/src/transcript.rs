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

//! Bind the completed sumcheck and packing execution as Polygero's source statement.
//!
//! Both roles sample this identifier after the packing response A. The
//! transcript already binds circuit identity, public inputs, commitments,
//! masked sumcheck messages and the packing reduction. Its fixed sampling
//! schedule determines the challenges used to derive those constraints.
//!
//! Polygero absorbs the identifier before its batching challenges. This makes
//! the handoff explicit without hashing sparse term order, zero coefficients or
//! compiled coordinates. The identifier is derived locally and is not serialized.

use crate::runtime::{
    proto::Digest,
    random::{RandomEngine, Transcript},
};

pub(super) fn statement_digest(transcript: &mut Transcript) -> Digest {
    transcript.write_bytes(b"longfellow-v2/polygero-statement/v1");
    Digest {
        data: transcript.bytes(32).try_into().unwrap(),
    }
}
