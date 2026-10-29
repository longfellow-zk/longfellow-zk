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

//! NEXT circuit decoding.
use crate::{
    core::proto::v2::Circuit,
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
pub fn decompress_circuits(
    bytes: &[u8],
    p: &P256Field,
    f: &Gf2_128Field,
    enforce: bool,
) -> Result<(Circuit<P256Field>, Circuit<Gf2_128Field>), String> {
    super::provider::decode(bytes, p, f, enforce)
}
#[cfg(test)]
#[path = "../../tests/v2_circuits.rs"]
mod tests;
