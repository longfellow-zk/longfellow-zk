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

pub const K_SIG_MAC_BIT_PLUCKER_V1: usize = 2;
pub const K_ZSTD_LEVEL: i32 = 16;

/// The Polygero dimensions `(k, s, n, t)` of the mdoc v2 joint commitment.
/// `zk_tool check-profiles` certifies its shared two-field budget separately
/// from the universal tuning catalog.
pub const MDOC_JOINT_PROFILE: (usize, usize, usize, usize) = (349, 12, 2443, 84);
