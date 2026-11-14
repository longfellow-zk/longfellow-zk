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

//! Version-neutral system discovery; never dispatches or implements proof execution.

#[cfg(feature = "v1")]
use super::v1;
use super::v2;
#[cfg(feature = "v1")]
pub const LONGFELLOW_V1: &str = v1::SYSTEM_ID;
pub const LONGFELLOW_V2: &str = v2::SYSTEM_ID;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSpecRef {
    #[cfg(feature = "v1")]
    V1(&'static v1::ZkSpecStruct),
    V2(&'static v2::ZkSpecStruct),
}
impl ZkSpecRef {
    #[must_use]
    pub fn version(self) -> usize {
        match self {
            #[cfg(feature = "v1")]
            Self::V1(s) => s.version,
            Self::V2(s) => s.version,
        }
    }
}
#[must_use]
pub fn find_zk_spec(system: &str, hash: &[u8; 32]) -> Option<ZkSpecRef> {
    match system {
        #[cfg(feature = "v1")]
        LONGFELLOW_V1 => v1::find_zk_spec(system, hash).map(ZkSpecRef::V1),
        LONGFELLOW_V2 => v2::find_zk_spec(system, hash).map(ZkSpecRef::V2),
        _ => None,
    }
}
#[must_use]
pub fn find_zk_spec_by_hex(system: &str, hash: &str) -> Option<ZkSpecRef> {
    match system {
        #[cfg(feature = "v1")]
        LONGFELLOW_V1 => v1::find_zk_spec_by_hex(system, hash).map(ZkSpecRef::V1),
        LONGFELLOW_V2 => v2::find_zk_spec_by_hex(system, hash).map(ZkSpecRef::V2),
        _ => None,
    }
}
