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

//! Preserve the existing polynomial-basis MAC with canonical polynomial packing.
use crate::{
    mdoc::proto::packed::HashInputManifest,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            AlgebraicField,
        },
        dual_packing::AffineClaim,
        zk_v2::packed::AuxiliaryBitClaim,
    },
};
pub fn mac_claims(
    manifest: &HashInputManifest,
    av: u128,
    tags: &[u128; 6],
    f: &F,
) -> Result<Vec<AuxiliaryBitClaim>, String> {
    manifest.validate()?;
    Ok((0..6)
        .map(|h| {
            let mut weights = vec![f.zero(); manifest.private_bits];
            for i in 0..128 {
                weights[manifest.mac_starts[h] + i] = f.mulf(&E::from(av), &E::from(1u128 << i));
            }
            AuxiliaryBitClaim {
                weights,
                rhs: AffineClaim {
                    constant: E::from(tags[h]),
                    terms: vec![(h, f.one())],
                },
            }
        })
        .collect())
}
