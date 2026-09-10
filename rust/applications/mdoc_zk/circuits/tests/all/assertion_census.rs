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

//! Enumerates every assertion `assert_valid_presentation_and_macs` emits, collapsed into
//! families by erasing the numeric indices in the scope path. This is the input to the
//! "meaning" layer: `formal/circuits/mdoc/Assertions.lean` has one Lean clause per family
//! below, and this census is what says the Lean list is complete.
//!
//! ```text
//! MDOC_ASSERTION_CENSUS_OUT=/tmp/census.txt \
//!   cargo test -p mdoc-zk-circuits --test circuits_tests assertion_census -- --nocapture
//! ```

#![allow(dead_code)]

use std::collections::BTreeMap;

use circuits_bitvec::BitvecLogic;
use compile_algebra::{gf2_128::Gf2_128Field, CompileNat};
use compile_logic::eval::EvalLogic;
use mdoc_zk_circuits::{
    hash::{derived, evaluate_derived, evaluate_given, given, hash_input_of_parsed_mdoc, HashMac,
           MdocHash},
    parse_test_data,
};

/// `a/b/b.0/c` and `a/b/b.17/c` are the same family. Also collapse a run of `x/x.N` into `x[]`
/// so the report reads like the source it came from.
fn family_of(path: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    for seg in path.split('/') {
        match seg.split_once('.') {
            // `foo.12` directly after `foo` is `assert_mapi`'s per-index child.
            Some((head, tail)) if tail.chars().all(|c| c.is_ascii_digit()) => {
                if parts.last().map(String::as_str) == Some(head) {
                    let n = parts.len();
                    parts[n - 1] = format!("{head}[]");
                } else {
                    parts.push(format!("{head}[]"));
                }
            }
            _ => parts.push(seg.to_string()),
        }
    }
    parts.join("/")
}

#[test]
fn assertion_census() {
    let fc = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&fc, &tracker);

    let mac_input = HashMac { mac_av: 3, mac_ap: [[5, 7]; 3] };
    let given = given::<4, _>(hash_input, mac_input);
    let derived = derived::<4, _>(&given);
    let mdoc = MdocHash::new(&l, given.hash_input.attrs.len());
    let bv = BitvecLogic::new(&l);
    let wire_given = evaluate_given(&l, &bv, &given);
    let wire_derived = evaluate_derived(&l, &bv, &derived);

    let assertions = mdoc.assert_valid_presentation_and_macs(&wire_given, &wire_derived);
    let fates = assertions.all_items();
    let paths = tracker.all_paths(&fates);

    let mut families: BTreeMap<String, usize> = BTreeMap::new();
    for p in &paths {
        *families.entry(family_of(p)).or_insert(0) += 1;
    }

    let mut report = String::new();
    report.push_str(&format!(
        "mdoc_hash assertion census\n\
         vector: mdoc_zk_testcases::vectors::TEST_DATA, {} disclosed attributes\n\
         total assertions: {}\n\
         distinct families: {}\n\n",
        given.hash_input.attrs.len(),
        paths.len(),
        families.len()
    ));
    report.push_str(&format!("{:>9}  family\n", "count"));
    let mut rows: Vec<(&String, &usize)> = families.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (fam, n) in rows {
        report.push_str(&format!("{n:>9}  {fam}\n"));
    }

    // A few sample paths per family, so a reader can see the index structure.
    report.push_str("\nsample paths\n");
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    for p in &paths {
        let f = family_of(p);
        let c = seen.entry(f).or_insert(0);
        if *c < 2 {
            report.push_str(&format!("  {p}\n"));
        }
        *c += 1;
    }

    print!("{report}");
    if let Ok(path) = std::env::var("MDOC_ASSERTION_CENSUS_OUT") {
        std::fs::write(&path, &report).expect("write census");
        eprintln!("wrote {path}");
    }

    assert!(!paths.is_empty());
}

/// The same census for `assert_signatures_and_macs`, the other half of the mdoc statement.
#[test]
fn assertion_census_signature() {
    use compile_algebra::{p256::P256Field, q256::Q256Field, secp256r1::Secp256r1};
    use mdoc_zk_circuits::signature::{
        derived as sig_derived, given as sig_given, signature_input_of_parsed_mdoc, MdocSignature,
        SignatureMac,
    };

    let f = P256Field::new();
    let curve = Secp256r1::new(&f);
    let (issuer_pk, parsed, _) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let sig = MdocSignature::new(&l, &curve);

    let sig_input = signature_input_of_parsed_mdoc(&parsed, issuer_pk);
    let mac_input = SignatureMac {
        mac_av: 0x112233445566778899aabbccddeeff00,
        mac_ap: [[0xabcdef0123456789abcdef0123456789, 0xfedcba9876543210fedcba9876543210]; 3],
    };
    let fn_field = Q256Field::new();
    let given = sig_given::<4, P256Field, _, _>(sig_input, mac_input, &f, &fn_field, &curve);
    let derived = sig_derived::<4, _, _, _>(&f, &fn_field, &curve, &given).unwrap();
    let bv = BitvecLogic::new(&l);
    let wire_given =
        mdoc_zk_circuits::signature::evaluate::evaluate_given::<Secp256r1<_>, _, _>(
            &l, &bv, &given, &f);
    let wire_derived =
        mdoc_zk_circuits::signature::evaluate::evaluate_derived::<Secp256r1<_>, _, _>(
            &l, &bv, &derived);

    let assertions = sig.assert_signatures_and_macs(&wire_given, &wire_derived);
    let fates = assertions.all_items();
    let paths = tracker.all_paths(&fates);

    let mut families: BTreeMap<String, usize> = BTreeMap::new();
    for p in &paths {
        *families.entry(family_of(p)).or_insert(0) += 1;
    }

    let mut report = String::new();
    report.push_str(&format!(
        "mdoc_signature assertion census\n\
         vector: mdoc_zk_testcases::vectors::TEST_DATA\n\
         total assertions: {}\n\
         distinct families: {}\n\n{:>9}  family\n",
        paths.len(),
        families.len(),
        "count"
    ));
    let mut rows: Vec<(&String, &usize)> = families.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (fam, n) in rows {
        report.push_str(&format!("{n:>9}  {fam}\n"));
    }
    print!("{report}");
    if let Ok(path) = std::env::var("MDOC_SIG_CENSUS_OUT") {
        std::fs::write(&path, &report).expect("write census");
    }
    assert!(!paths.is_empty());
}
