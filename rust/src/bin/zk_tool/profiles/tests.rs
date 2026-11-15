// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
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
            r["certificate_overlap"] = Value::from(small(&r, "certificate_overlap").unwrap() + 1);
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
