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

//! Independent exact checks of the compiled catalogs and shared Hahn manifest.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    str::FromStr,
};

use longfellow_zk::compile::polygero::profiles as gero;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use serde_json::Value;

use crate::{
    exact::{choose, evaluate, pow2, Q},
    require, root, Result,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Protocol {
    Polygero,
}
impl Protocol {
    pub(crate) fn parse(value: &str) -> Result<Self> {
        match value {
            "polygero" => Ok(Self::Polygero),
            _ => Err("protocol must be polygero".into()),
        }
    }
    pub(crate) fn name(self) -> &'static str {
        "polygero"
    }
    pub(crate) fn namespace(self) -> &'static str {
        "Polygero"
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Profile {
    pub k: usize,
    pub s: usize,
    pub n: usize,
    pub t: usize,
}
impl Profile {
    pub(crate) fn label(self) -> String {
        format!("{}_{}_{}_{}", self.k, self.s, self.n, self.t)
    }
}
pub(crate) struct Audit {
    pub profiles: Vec<Profile>,
    pub hahn: BTreeMap<Profile, Value>,
    pub joint: Value,
}

pub(crate) fn integer(value: &Value) -> Result<BigInt> {
    require(value.is_number(), "expected a JSON integer")?;
    Ok(BigInt::from_str(&value.to_string()).map_err(|_| "expected an exact JSON integer")?)
}
fn small(row: &Value, name: &str) -> Result<usize> {
    Ok(row[name]
        .as_u64()
        .ok_or_else(|| format!("invalid {name}"))?
        .try_into()?)
}
fn rational(value: &Value) -> Result<Q> {
    let parts = value.as_array().ok_or("expected rational pair")?;
    require(parts.len() == 2, "expected rational pair")?;
    let denominator = integer(&parts[1])?;
    require(
        denominator > BigInt::zero(),
        "rational denominator must be positive",
    )?;
    Ok(Q::new(integer(&parts[0])?, denominator))
}
/// Use the three-term recurrence, independently of the hypergeometric search.
fn kernels(n: usize, w: usize, degree: usize) -> Vec<Vec<Q>> {
    let mut polynomials = vec![vec![Q::int(1)]];
    let mut previous_a = Q::int(0);
    for j in 0..degree {
        let a = Q::new(
            BigInt::from(n - j + 1) * (w - j) * (n - w - j),
            BigInt::from(n - 2 * j) * (n - 2 * j + 1),
        );
        let multiplicity = |d: usize| {
            choose(n, d)
                - if d == 0 {
                    BigInt::zero()
                } else {
                    choose(n, d - 1)
                }
        };
        let c = if j == 0 {
            Q::int(0)
        } else {
            previous_a.mul(&Q::new(multiplicity(j - 1), multiplicity(j)))
        };
        let b = Q::int(w).sub(&a).sub(&c);
        let mut out = vec![Q::int(0); j + 2];
        for (i, coefficient) in polynomials[j].iter().enumerate() {
            out[i] = out[i].sub(&b.mul(coefficient).div(&a));
            out[i + 1] = out[i + 1].add(&coefficient.div(&a));
        }
        if j > 0 {
            for (i, coefficient) in polynomials[j - 1].iter().enumerate() {
                out[i] = out[i].sub(&c.mul(coefficient).div(&a));
            }
        }
        polynomials.push(out);
        previous_a = a;
    }
    polynomials
}
fn gram_diagonal(n: usize, w: usize, degree: usize) -> Q {
    (0..=degree).fold(Q::int(0), |total, i| {
        let ratio = Q::new(choose(n + i - w - degree, i), choose(w, i));
        total.add(
            &ratio
                .square()
                .mul(&Q::int(choose(w, i) * choose(n - w, degree - i))),
        )
    })
}

/// Reconstruct the packing polynomial independently and check its signs and list cap.
fn verify_polynomial(row: &Value, n: usize, w: usize, lambda: usize, count: &BigInt) -> Result<()> {
    let weights: Vec<_> = row["coefficients"]
        .as_array()
        .ok_or("missing coefficients")?
        .iter()
        .map(integer)
        .collect::<Result<_>>()?;
    require(
        !weights.is_empty()
            && weights.len() <= w + 1
            && weights[0] > BigInt::zero()
            && weights.iter().all(|x| x >= &BigInt::zero()),
        "invalid Hahn coefficients",
    )?;
    let mut polynomial = vec![Q::int(0); weights.len()];
    for (d, (weight, kernel)) in weights
        .iter()
        .zip(kernels(n, w, weights.len() - 1))
        .enumerate()
    {
        let scale = Q::int(weight.clone()).mul(&gram_diagonal(n, w, d));
        for (i, coefficient) in kernel.iter().enumerate() {
            polynomial[i] = polynomial[i].add(&scale.mul(coefficient));
        }
    }
    let expected: Vec<_> = row["polynomial"]
        .as_array()
        .ok_or("missing polynomial")?
        .iter()
        .map(rational)
        .collect::<Result<_>>()?;
    require(
        polynomial == expected,
        "Hahn polynomial does not match independent recurrence",
    )?;
    require(
        (0..=lambda).all(|x| evaluate(&polynomial, x) <= Q::int(0)),
        "positive overlap polynomial",
    )?;
    require(
        evaluate(&polynomial, w)
            .div(&Q::int(weights[0].clone()))
            .floor()
            == *count,
        "incorrect list-size bound",
    )?;
    Ok(())
}

/// Verify all finite hypotheses before accepting a manifest's list-size cap.
pub(crate) fn check_hahn(row: &Value) -> Result<Profile> {
    require(
        row.get("field_min").is_none(),
        "field-specific profiles are unsupported",
    )?;
    let theta = Q::new(BigInt::one(), pow2(130));
    let (n, k, s, t) = (
        small(row, "n")?,
        small(row, "k")?,
        small(row, "s")?,
        small(row, "t")?,
    );
    require(
        n <= 1 << 28 && k > 0 && k <= n && s <= n && t > 0 && t <= n,
        "invalid manifest dimensions",
    )?;
    let cutoff = small(row, "cutoff")?;
    let count = integer(&row["count"])?;
    let u = integer(&row["index"])?;
    let overlap = k + 2 * s - 1;
    let w = if row.get("certificate_weight").is_some() {
        small(row, "certificate_weight")?
    } else {
        cutoff
    };
    let lambda = if row.get("certificate_overlap").is_some() {
        small(row, "certificate_overlap")?
    } else {
        overlap
    };
    require(
        cutoff >= usize::max(k + 2 * s + 1, 2 * k + s) && cutoff <= n,
        "invalid cutoff",
    )?;
    if w != cutoff {
        require(
            w == n - cutoff && n + overlap >= 2 * cutoff && lambda == n + overlap - 2 * cutoff,
            "invalid complement geometry",
        )?;
    } else {
        require(lambda == overlap, "invalid overlap")?;
    }
    require(lambda < w && w <= n / 2, "invalid Hahn weight/overlap")?;
    require(
        count > 1.into() && count <= pow2(128) && u >= 1.into() && u <= count,
        "invalid count/index",
    )?;
    verify_polynomial(row, n, w, lambda, &count)?;
    require(
        choose(n, k + 2 * s + 1) * 4 <= pow2(128).pow(s as u32),
        "rank budget failed",
    )?;
    let denominator = choose(n, t);
    require(
        Q::new(choose(cutoff - 1, t), denominator.clone()) <= theta,
        "opening floor failed",
    )?;
    let excess = Q::new(&u - 1, BigInt::from(2) * (&count - 1))
        .add(&Q::new(count, BigInt::from(2) * u).mul(&Q::new(choose(overlap, t), denominator)));
    require(excess <= theta, "opening excess failed")?;
    Ok(Profile { k, s, n, t })
}
pub(crate) fn manifest() -> Result<Vec<Value>> {
    let value: Value = serde_json::from_slice(&fs::read(
        root().join("tools/parameters/hahn/profiles.json"),
    )?)?;
    Ok(value["profiles"]
        .as_array()
        .ok_or("missing profiles")?
        .clone())
}

pub(crate) fn joint_manifest() -> Result<Value> {
    let value: Value = serde_json::from_slice(&fs::read(
        root().join("tools/parameters/hahn/profiles.json"),
    )?)?;
    value
        .get("mdoc_joint")
        .cloned()
        .ok_or_else(|| "missing joint mdoc profile".into())
}

pub(crate) fn joint_profile() -> Profile {
    let (k, s, n, t) = gero::MDOC_JOINT_PROFILE;
    Profile { k, s, n, t }
}

/// Audit the production two-field composition using its certified list caps.
/// These are joint-query charges, not the universal tuning profile's 2^-130
/// opening contract. `--check-lean` additionally binds these caps to Lean's
/// production certificate; `certify-hahn` checks its three Hahn proofs.
pub(crate) fn check_joint(row: &Value) -> Result<Profile> {
    require(
        row["name"] == "MdocJoint" && row["certificate"] == "MdocJointProfile.profile",
        "unexpected production mdoc certificate reference",
    )?;
    let p = Profile {
        k: small(row, "k")?,
        s: small(row, "s")?,
        n: small(row, "n")?,
        t: small(row, "t")?,
    };
    require(
        p == joint_profile(),
        "joint mdoc geometry differs from production",
    )?;
    let active = small(row, "active_cutoff")?;
    let binary = small(row, "binary_cutoff")?;
    let prime = small(row, "prime_cutoff")?;
    let active_list = integer(&row["active_list"])?;
    let binary_list = integer(&row["binary_list"])?;
    let prime_list = integer(&row["prime_list"])?;
    let q = pow2(128);
    let prime_order = pow2(256) - pow2(224) + pow2(192) + pow2(96) - 1;
    require(
        p.k > 2 * p.t && p.s > 0 && p.t > 0 && p.n == 7 * p.k,
        "invalid joint mdoc profile",
    )?;
    require(
        (p.k + 2 * p.s + 1).max(2 * p.k + p.s) <= active
            && active <= p.n
            && p.k <= binary
            && binary <= p.n
            && p.k <= prime
            && prime <= p.n,
        "invalid joint cutoffs",
    )?;
    require(
        [&active_list, &binary_list, &prime_list]
            .iter()
            .all(|cap| **cap >= BigInt::one() && **cap <= q),
        "invalid joint list caps",
    )?;
    let tail = |columns| Q::new(choose(columns, p.t), choose(p.n, p.t));
    let ordinary = Q::new(2.into(), &q - 1);
    require(
        Q::new(active_list.clone(), 2.into()).mul(&tail(p.k + 2 * p.s - 1)) <= tail(active - 1),
        "joint active threshold condition failed",
    )?;
    let opening = tail(active - 1)
        .add(&tail(binary + p.s - 1))
        .add(&tail(prime + p.s - 1));
    require(opening <= ordinary, "joint opening budget failed")?;
    let rows = choose(p.n, p.k + 2 * p.s + 1);
    let rank = |field: &BigInt| Q::new(rows.clone(), field.pow((p.s + 1) as u32));
    let mass = Q::int(1).add(&Q::int(&active_list - 1).mul(&tail(active - 1)));
    let parent = rank(&q).add(&rank(&prime_order)).add(
        &Q::new(1.into(), q.clone())
            .add(&Q::new(1.into(), prime_order.clone()))
            .mul(&mass),
    );
    require(parent < ordinary, "joint parent budget failed")?;
    let fingerprint = Q::new(
        &binary_list * (&binary_list - 1),
        BigInt::from(2) * q.pow(2),
    )
    .add(&Q::new(
        &prime_list * (&prime_list - 1),
        BigInt::from(2) * prime_order.pow(2),
    ));
    require(fingerprint <= ordinary, "joint fingerprint budget failed")?;
    Ok(p)
}
pub(crate) fn catalog(protocol: Protocol) -> Vec<Profile> {
    let (queries, fixed, r7, r4) = match protocol {
        Protocol::Polygero => (
            gero::TUNING_QUERIES,
            gero::TUNING_PROFILES,
            gero::RATE7_PROFILES,
            gero::RATE4_PROFILES,
        ),
    };
    let mut out: Vec<_> = fixed
        .iter()
        .map(|&(k, s, n)| Profile {
            k,
            s,
            n,
            t: queries,
        })
        .collect();
    for (rate, rows) in [(7, r7), (4, r4)] {
        out.extend(rows.iter().map(|&(k, s, t)| Profile {
            k,
            s,
            n: rate * k,
            t,
        }));
    }
    out.push(joint_profile());
    out
}
fn baseline_budget(p: Profile) -> bool {
    let theta = Q::new(1.into(), pow2(130));
    let denominator = choose(p.n, p.t);
    Q::new(
        choose(usize::max(p.k + 2 * p.s + 1, 2 * p.k + p.s) - 1, p.t),
        denominator.clone(),
    ) <= theta
        && Q::new(choose(p.k + 2 * p.s - 1, p.t), denominator) <= theta.square()
}
pub(crate) fn audit(protocol: Protocol) -> Result<Audit> {
    let profiles = catalog(protocol);
    let joint = joint_manifest()?;
    let joint_geometry = check_joint(&joint)?;
    let rows = manifest()?;
    let mut hahn = BTreeMap::new();
    let names: BTreeSet<_> = rows
        .iter()
        .map(|r| r["name"].as_str().unwrap_or(""))
        .collect();
    require(
        names == BTreeSet::from(["Hash", "Signature"]),
        "unexpected Hahn inventory",
    )?;
    for row in rows {
        let p = check_hahn(&row)?;
        require(
            profiles.contains(&p),
            "manifest profile missing from runtime catalog",
        )?;
        require(hahn.insert(p, row).is_none(), "duplicate manifest profile")?;
    }
    for &p in &profiles {
        if p == joint_geometry {
            continue;
        }
        let Profile { k, s, n, t } = p;
        require(
            k > 2 * t && t > 0 && usize::max(k + 2 * s + 1, 2 * k + s) <= n,
            "profile geometry failed",
        )?;
        let q = pow2(128);
        require(
            choose(n, k + 2 * s + 1) * 4 <= q.pow(s as u32),
            "profile rank budget failed",
        )?;
        if !hahn.contains_key(&p) {
            require(baseline_budget(p), "profile second-moment budget failed")?;
        }
        let rate_family = n == 4 * k || n == 7 * k;
        if rate_family {
            require(
                (0..s).all(|j| choose(n, k + 2 * j + 1) * 4 > q.pow(j as u32)),
                "masking degree is not minimal",
            )?;
            if !hahn.contains_key(&p) {
                require(
                    (1..t).all(|j| !baseline_budget(Profile { t: j, ..p })),
                    "opening count is not minimal",
                )?;
            }
        }
    }
    Ok(Audit {
        profiles,
        hahn,
        joint,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn all_manifests_and_catalog() {
        let a = audit(Protocol::Polygero).unwrap();
        assert_eq!(a.profiles.len(), 64);
        assert_eq!(a.hahn.len(), 2);
        assert_eq!(check_joint(&a.joint).unwrap(), joint_profile());
    }
    #[test]
    fn joint_profile_budget_changes_reject() {
        let mut row = joint_manifest().unwrap();
        row["active_list"] = serde_json::from_str(&pow2(128).to_string()).unwrap();
        assert!(check_joint(&row).is_err());
        let mut row = joint_manifest().unwrap();
        row["t"] = Value::from(joint_profile().t - 1);
        assert!(check_joint(&row).is_err());
    }
    #[test]
    fn fewer_openings_reject() {
        for mut r in manifest().unwrap() {
            r["t"] = Value::from(small(&r, "t").unwrap() - 1);
            assert!(check_hahn(&r).is_err());
        }
    }
    #[test]
    fn wrong_complement_rejects() {
        for mut r in manifest().unwrap() {
            if r.get("certificate_weight").is_some() {
                r["certificate_overlap"] =
                    Value::from(small(&r, "certificate_overlap").unwrap() + 1);
                assert!(check_hahn(&r).is_err());
            }
        }
    }
    #[test]
    fn field_specific_profiles_reject() {
        let mut row = manifest().unwrap().remove(0);
        row["field_min"] = serde_json::json!(17);
        assert!(check_hahn(&row).is_err());
    }
    #[test]
    fn negative_weight_rejects() {
        let mut r = manifest().unwrap().remove(0);
        r["coefficients"][1] = Value::from(-1);
        assert!(check_hahn(&r).is_err());
    }
    #[test]
    fn incorrect_list_size_rejects() {
        let mut r = manifest().unwrap().remove(0);
        r["count"] =
            serde_json::from_str(&(integer(&r["count"]).unwrap() - 1_u32).to_string()).unwrap();
        assert!(check_hahn(&r).is_err());
    }
    #[test]
    fn malformed_rationals_reject() {
        assert!(rational(&serde_json::json!([1, 0])).is_err());
        assert!(integer(&serde_json::json!(1.5)).is_err());
    }
}
