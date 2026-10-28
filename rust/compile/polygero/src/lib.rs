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

//! Select Polygero dimensions when preparing a compiled application specification.
//!
//! Public witness layout and encoding sizes determine the estimated proof cost.
//! The caller supplies an interpolation-capacity predicate, optionally restricted
//! by a public resource budget. Selection is deterministic within the checked
//! catalog; the resulting k, s, n, t are stored in the specification.
//! Circuit compilation and protocol execution remain independent of this policy.

pub mod profiles;

use profiles::*;

use crate::runtime::proto::polygero::{
    PolygeroConfig, PolygeroGeometry, PolygeroProductConstraint,
};

/// Minimize a conservative wire-size estimate within an audited family.
/// The caller must use a field of cardinality at least 2^128. Every profile
/// satisfies the fixed counting budgets in the offline Rust tool.
/// `zk_tool check-profiles --protocol polygero --check-lean <FORMAL>`
/// checks every shipped profile against the concrete one-level FS theorem.
/// This does not certify the complete Rust implementation or Merkle binding.
/// `accept` must check the interpolation backend's capacity. All opened rows
/// use the ambient field encoding.
pub fn tune_large_field(
    nw: usize,
    products: &[PolygeroProductConstraint],
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
        products,
        field_bytes,
        accept,
    )
}

/// Tune at a fixed ordinary code rate k/n, with independently optimized
/// masking degree and opening count. The audited families support inverse
/// rates 4 (MLDSA) and 7 (v8), matching their Ligero profiles. Other rates
/// return None.
/// The field-size and certification limits of `tune_large_field` apply.
pub fn tune_large_field_at_rate(
    rateinv: usize,
    nw: usize,
    products: &[PolygeroProductConstraint],
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
        products,
        field_bytes,
        accept,
    )
}

/// Select profiles for MLDSA's concrete sextic field, q = 8,380,417^6.
/// These profiles must not be used with a different field.
/// The checked coefficient, including rank and batching errors, is at most 2^-128.
#[cfg(feature = "experimental")]
pub fn tune_mldsa_128(
    nw: usize,
    products: &[PolygeroProductConstraint],
    accept: impl Fn(PolygeroConfig) -> bool,
) -> Option<PolygeroConfig> {
    tune_profiles(
        MLDSA_PROFILES
            .iter()
            .map(|&(k, s, t)| PolygeroConfig { k, s, n: 4 * k, t }),
        nw,
        products,
        crate::core::algebra::fp24_ext6::SERIALIZED_SIZE,
        accept,
    )
}

fn tune_profiles(
    profiles: impl Iterator<Item = PolygeroConfig>,
    nw: usize,
    products: &[PolygeroProductConstraint],
    field_bytes: usize,
    accept: impl Fn(PolygeroConfig) -> bool,
) -> Option<PolygeroConfig> {
    if field_bytes == 0
        || products
            .iter()
            .any(|p| [p.x, p.y, p.z].iter().any(|&w| w >= nw))
    {
        return None;
    }
    profiles
        .filter(|&config| accept(config))
        .filter_map(|config| {
            let geom = PolygeroGeometry {
                nw,
                nq: products.len(),
                k: config.k,
                s: config.s,
                n: config.n,
                t: config.t,
            };
            if geom.validate().is_err() {
                return None;
            }
            let column_bytes = geom.transmitted_rows() as u128 * field_bytes as u128;
            let responses = geom.response_lengths().iter().sum::<usize>() as u128;
            // Maximum shared frontier for distinct queries in a binary tree.
            let query_level = config.t.next_power_of_two().ilog2() as usize;
            let frontier = config.t * (config.n.next_power_of_two().ilog2() as usize - query_level)
                + (1 << query_level)
                - config.t;
            let bytes = responses * field_bytes as u128
                + config.t as u128 * (column_bytes + 32)
                + 32 * frontier as u128;
            Some((config, bytes))
        })
        .min_by_key(|&(_, bytes)| bytes)
        .map(|(config, _)| config)
}

#[cfg(test)]
#[path = "../tests/parameters.rs"]
mod tests;
