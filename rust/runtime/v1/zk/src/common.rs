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

//! Field and interpolation context shared by the two v1 protocol roles.

use crate::runtime::{
    algebra::{RangeInterpolatorFactory, ZkField},
    proto::Digest,
};

/// Bundles the field implementation and the interpolator factory.
pub struct ZkContext<'a, const W: usize, F: ZkField<W>, IF: RangeInterpolatorFactory<W, F>> {
    pub f: &'a F,
    pub make_interpolator: &'a IF,
}

/// Fixed Ligero statement tag used by the legacy protocol. The circuit and
/// public inputs are absorbed earlier by the sumcheck transcript; these exact
/// bytes must remain unchanged for compatibility with existing proofs.
pub const DEFAULT_STATEMENT_HASH: Digest = Digest {
    data: [
        0xde, 0xad, 0xbe, 0xef, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0,
    ],
};
