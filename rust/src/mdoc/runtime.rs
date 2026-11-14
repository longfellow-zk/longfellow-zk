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

//! System selection only; proof execution and encoding live under v1 or v2.

#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod fields;
#[cfg(feature = "v1")]
pub mod v1;
pub mod v2;
mod zk_spec;
#[cfg(feature = "v1")]
pub use zk_spec::LONGFELLOW_V1;
pub use zk_spec::{find_zk_spec, find_zk_spec_by_hex, ZkSpecRef, LONGFELLOW_V2};

#[cfg(test)]
mod tests;
