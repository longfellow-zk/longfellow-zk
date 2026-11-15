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

pub mod archive;
mod metadata;
mod reader;
mod stream;
mod uleb;
pub mod v1;
pub mod v2;

pub use uleb::*;

/// The most sumcheck rounds in one layer, a proof-format limit shared by v1
/// and v2.
pub const MAX_LOGW: usize = 40;

/// Whether a layer's round count is valid: at most `MAX_LOGW`, and below the
/// host's `usize::BITS` so that `2^logw` wires are addressable.
#[inline]
#[must_use]
pub const fn sane_logw(logw: usize) -> bool {
    logw <= MAX_LOGW && logw < (usize::BITS as usize)
}

pub use metadata::{CircuitGeometry, DigestBytes};
pub use stream::Stream;

#[cfg(test)]
mod tests;
