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

//! Shared circuit-reader resource limits.

// Reader hardening constants: dimensioned for 5 million max wires and 20 million max terms
pub(in crate::core::proto) const MAX_WIRES: usize = 5_000_000;
pub(in crate::core::proto) const MAX_TERMS_PER_LAYER: usize = 20_000_000;
pub(in crate::core::proto) const MAX_TOTAL_TERMS: usize = 20_000_000;
pub(in crate::core::proto) const MAX_DELTAS: usize = 20_000_000;
pub(in crate::core::proto) const MAX_CONSTANTS: usize = 5_000_000;
pub(in crate::core::proto) const MAX_LAYERS: usize = 10_000;
pub(in crate::core::proto) const MAX_LAYER_INPUTS: usize = 5_000_000;
