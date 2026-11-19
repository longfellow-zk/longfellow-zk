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

//! The audited Polygero catalog and profile tuning.
//!
//! The catalog lists the dimensions `(k, s, n, t)` whose soundness budgets
//! `check-profiles` audits exactly and, with `--check-lean`, in Lean. Tuning
//! picks the profile with the smallest estimated proof for a witness size and
//! field width; applications record the profile they chose in their
//! specification (for mdoc, `mdoc::v2::MDOC_JOINT_PROFILE`).

use longfellow_zk::runtime::v2::proto::{
    polygero::{PolygeroConfig, PolygeroGeometry},
    NONCE_LEN,
};

/// Opening count shared by the variable-rate family.
pub const TUNING_QUERIES: usize = 80;
/// Variable-rate candidates (k, s, n), all using `TUNING_QUERIES` openings.
pub const TUNING_PROFILES: &[(usize, usize, usize)] = &[
    (192, 64, 8192),
    (224, 64, 8192),
    (256, 64, 8192),
    (288, 64, 8192),
    (320, 64, 8192),
    (352, 64, 8192),
    (384, 64, 8192),
    (416, 64, 8192),
    (448, 64, 8192),
    (480, 64, 8192),
    (512, 64, 8192),
    (640, 80, 16384),
    (768, 96, 16384),
    (896, 112, 16384),
    (1024, 128, 32768),
    (1152, 144, 32768),
    (1280, 160, 32768),
    (1408, 176, 32768),
    (1536, 192, 32768),
];

// Match the ordinary Reed-Solomon rate of the v8 Ligero profiles: n = 7*k.
// Each (k, s, t) uses the least s satisfying the universal rank certificate,
// then tune t under the second-moment or checked Hahn certificate; e = t.
// Hahn entries are bounded-search results, not claimed globally optimal.
// The exact checker audits this geometry independently of the other protocols.
pub const RATE7_PROFILES: &[(usize, usize, usize)] = &[
    (192, 7, 87),
    (224, 8, 88),
    (256, 9, 89),
    (288, 10, 90),
    (320, 11, 90),
    (352, 12, 91),
    (384, 13, 91),
    (416, 15, 86),
    (448, 16, 92),
    (480, 17, 92),
    (512, 18, 87),
    (640, 22, 93),
    (768, 26, 94),
    (896, 31, 94),
    (1024, 35, 94),
    (1152, 39, 95),
    (1280, 44, 95),
    (1408, 48, 95),
    (1536, 52, 95),
];

// Additional profiles at ordinary code rate 1/4. As above,
// Minimize s for the universal rank certificate; use checked Hahn counts
// where available, and second-moment counts for the remaining widths.
pub const RATE4_PROFILES: &[(usize, usize, usize)] = &[
    (288, 8, 123),
    (320, 9, 124),
    (352, 10, 124),
    (384, 10, 125),
    (416, 11, 126),
    (448, 12, 126),
    (480, 13, 127),
    (512, 14, 127),
    (576, 15, 128),
    (640, 17, 128),
    (704, 19, 129),
    (768, 20, 129),
    (832, 22, 130),
    (896, 24, 130),
    (960, 25, 130),
    (992, 26, 131),
    (1024, 27, 131),
    (1088, 29, 131),
    (1152, 30, 131),
    (1216, 32, 132),
    (1280, 34, 132),
    (1408, 37, 132),
    (1536, 40, 132),
    (1792, 47, 133),
    (2048, 54, 133),
];

/// Minimize a conservative wire-size estimate within an audited family.
/// The caller must use a field of cardinality at least 2^128. Every profile
/// satisfies the fixed counting budgets in the offline Rust tool.
/// `zk_tool check-profiles --protocol polygero --check-lean <FORMAL>`
/// checks every shipped profile against the concrete one-level FS theorem.
/// This does not certify the complete Rust implementation or Merkle binding.
/// `accept` must check the interpolation backend's capacity.
pub fn tune_large_field(
    nw: usize,
    field_bytes: usize,
    accept: impl Fn(PolygeroConfig) -> bool,
) -> Option<PolygeroConfig> {
    tune_profiles(
        TUNING_PROFILES.iter().map(|&(k, s, n)| PolygeroConfig {
            k,
            s,
            n,
            t: TUNING_QUERIES,
        }),
        nw,
        field_bytes,
        accept,
    )
}

/// Tune at a fixed ordinary code rate k/n, with independently optimized
/// masking degree and opening count. The audited families support inverse
/// rates 4 and 7 (v8), matching their Ligero profiles. Other rates
/// return None.
/// The field-size and certification limits of `tune_large_field` apply.
pub fn tune_large_field_at_rate(
    rateinv: usize,
    nw: usize,
    field_bytes: usize,
    accept: impl Fn(PolygeroConfig) -> bool,
) -> Option<PolygeroConfig> {
    let profiles = match rateinv {
        4 => RATE4_PROFILES,
        7 => RATE7_PROFILES,
        _ => return None,
    };
    tune_profiles(
        profiles.iter().map(|&(k, s, t)| PolygeroConfig {
            k,
            s,
            n: rateinv * k,
            t,
        }),
        nw,
        field_bytes,
        accept,
    )
}

fn tune_profiles(
    profiles: impl Iterator<Item = PolygeroConfig>,
    nw: usize,
    field_bytes: usize,
    accept: impl Fn(PolygeroConfig) -> bool,
) -> Option<PolygeroConfig> {
    if field_bytes == 0 {
        return None;
    }
    profiles
        .filter(|&config| accept(config))
        .filter_map(|config| Some((config, estimated_proof_bytes(config, nw, field_bytes)?)))
        .min_by_key(|&(_, bytes)| bytes)
        .map(|(config, _)| config)
}

/// A conservative proof-size estimate for `config` over `nw` witnesses in a
/// field of `field_bytes` bytes: the responses, the opened columns with
/// their nonces, and the largest shared Merkle frontier. None if the
/// geometry is invalid.
pub fn estimated_proof_bytes(
    config: PolygeroConfig,
    nw: usize,
    field_bytes: usize,
) -> Option<u128> {
    let geom = PolygeroGeometry::new(nw, config).ok()?;
    let column_bytes = geom.nrow() as u128 * field_bytes as u128;
    let responses = geom.response_lengths().iter().sum::<usize>() as u128;
    // Maximum shared frontier for distinct queries in a binary tree.
    let query_level = config.t.next_power_of_two().ilog2() as usize;
    let frontier = config.t * (config.n.next_power_of_two().ilog2() as usize - query_level)
        + (1 << query_level)
        - config.t;
    Some(
        responses * field_bytes as u128
            + config.t as u128 * (column_bytes + NONCE_LEN as u128)
            + 32 * frontier as u128,
    )
}

#[cfg(test)]
mod tests;
