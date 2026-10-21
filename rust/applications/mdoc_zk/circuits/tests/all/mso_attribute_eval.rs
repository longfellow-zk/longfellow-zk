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

use circuits_bitvec::{BitvecLogic, V8};
use compile_algebra::gf2_128::Gf2_128Field;
use compile_logic::{
    eval::{EvalAssertions, EvalLogic},
    tracker::AssertionTracker,
};
use mdoc_zk_circuits::mso_attribute::{
    circuit::{AttrSlice, AttributeVerifier, DisclosedAttribute, FieldLocator},
    constants::K_ATTR_INDEX_BITS,
    pnym::{ConcreteDerived as PnymConcreteDerived, ConcreteGiven as PnymConcreteGiven},
};
use mso_attribute_corruptors::MsoAttributeMockGiven;

use super::mso_attribute_corruptors;

#[test]
fn test_prefix_equal_boundary_bug() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);

    let bv = BitvecLogic::new(&l);
    let verifier = AttributeVerifier::new(&l);

    // Create got and want of size 51
    let mut got = Vec::new();
    let mut want = Vec::new();
    for _ in 0..50 {
        got.push(bv.of_u8(0));
        want.push(bv.of_u8(0));
    }
    // Make them differ at index 50 (the 51st byte)
    got.push(bv.of_u8(1));
    want.push(bv.of_u8(0));

    let len = bv.of_u64::<K_ATTR_INDEX_BITS>(51);

    // Test with max = 50: should succeed (does not compare index 50)
    let assertions_50 = verifier.assert_prefix_equal(50, &got, &want, &len);
    assertions_50.unwrap();

    // Test with max = 51: should fail (compares index 50 and finds mismatch)
    let assertions_51 = verifier.assert_prefix_equal(51, &got, &want, &len);
    assert!(assertions_51.is_err());
}

#[test]
fn test_prefix_equal_vlen_boundary_bug() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);

    let bv = BitvecLogic::new(&l);
    let verifier = AttributeVerifier::new(&l);

    // Create got and want of size 78
    let mut got = Vec::new();
    let mut want = Vec::new();
    for _ in 0..77 {
        got.push(bv.of_u8(0));
        want.push(bv.of_u8(0));
    }
    // Make them differ at index 77 (the 78th byte)
    got.push(bv.of_u8(1));
    want.push(bv.of_u8(0));

    let len = bv.of_u64::<K_ATTR_INDEX_BITS>(78);

    // Test with max = 77: should succeed (does not compare index 77)
    let assertions_77 = verifier.assert_prefix_equal(77, &got, &want, &len);
    assertions_77.unwrap();

    // Test with max = 78: should fail (compares index 77 and finds mismatch)
    let assertions_78 = verifier.assert_prefix_equal(78, &got, &want, &len);
    assert!(assertions_78.is_err());
}

fn run_attribute_test_mock<'a, F>(
    f: &'a Gf2_128Field,
    tracker: &'a compile_logic::tracker::AssertionTracker,
    mutate_f: F,
) -> compile_logic::eval::EvalAssertions<'a>
where
    F: FnOnce(&mut MsoAttributeMockGiven),
{
    let mut mock = MsoAttributeMockGiven {
        raw_buf: vec![
            0xd8, 0x18, 0x58, 0x60, 0xa4, // headers
            0x68, b'd', b'i', b'g', b'e', b's', b't', b'I', b'D', 0x00, // digestID
            0x66, b'r', b'a', b'n', b'd', b'o', b'm', // random key
            0x58, 0x20, // byte string 32
            0x22, 0x31, 0x18, 0x3c, 0x7d, 0x9f, 0x4d, 0x2e, 0x2e, 0x14, 0x6d, 0x24, 0x84, 0x58,
            0xb4, 0xcc, 0xe9, 0x48, 0x79, 0x8f, 0xda, 0x82, 0x40, 0xd3, 0x60, 0xa8, 0xf4, 0x0f,
            0x6d, 0x75, 0x48, 0xd3, 0x71, b'e', b'l', b'e', b'm', b'e', b'n', b't', b'I', b'd',
            b'e', b'n', b't', b'i', b'f', b'i', b'e', b'r', // key
            0x6b, b'a', b'g', b'e', b'_', b'o', b'v', b'e', b'r', b'_', b'1',
            b'8', // age_over_18
            0x6c, b'e', b'l', b'e', b'm', b'e', b'n', b't', b'V', b'a', b'l', b'u',
            b'e', // key
            0xf5, // true
        ],
        slot_position: [5, 15, 56, 86],
        length: [10, 41, 30, 14],
        permutation: [0, 1, 2, 3],
        disclosed_name: {
            let mut name = vec![0x60 + 11];
            name.extend_from_slice(b"age_over_18");
            name
        },
        disclosed_name_len: 12,
        disclosed_value: vec![0xf5],
        disclosed_value_len: 1,
        op: 0,
        preimage_len: 100,
    };

    mutate_f(&mut mock);

    type L<'a> = EvalLogic<'a, Gf2_128Field>;
    let l = EvalLogic::new_with_tracker(f, tracker);
    let bv = BitvecLogic::new(&l);

    use mdoc_zk_circuits::mso_attribute::constants::K_ATTR_PREIMAGE_LEN;
    let (nblocks, length_bytes, padded_preimage) =
        circuits_sha256msg::concrete::pad_sha256_message(&mock.raw_buf, 2).unwrap();
    let attribute_preimage = padded_preimage
        .iter()
        .map(|&b| bv.of_u8(b))
        .collect::<Vec<_>>();
    let zero_v8 = bv.of_u8(0);

    let mut oa_attr = std::array::from_fn(|_| zero_v8.clone());
    for (slot, &b) in oa_attr.iter_mut().zip(mock.disclosed_name.iter().take(32)) {
        *slot = bv.of_u8(b);
    }

    let mut oa_v1 = std::array::from_fn(|_| zero_v8.clone());
    for (slot, &b) in oa_v1.iter_mut().zip(mock.disclosed_value.iter().take(64)) {
        *slot = bv.of_u8(b);
    }

    let da = DisclosedAttribute {
        expected_name: AttrSlice {
            data: oa_attr,
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(mock.disclosed_name_len),
        },
        expected_cbor_value: AttrSlice {
            data: oa_v1,
            len: bv.of_u64::<K_ATTR_INDEX_BITS>(mock.disclosed_value_len),
        },
        op: bv.of_u64::<2>(mock.op),
    };

    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|i| {
            bv.of_u64::<K_ATTR_INDEX_BITS>(mock.slot_position[i])
        }),
        length: std::array::from_fn(|i| bv.of_u64::<K_ATTR_INDEX_BITS>(mock.length[i])),
        permutation: std::array::from_fn(|i| bv.of_u64::<2>(mock.permutation[i])),
    };

    let preimage_array: [V8<L>; K_ATTR_PREIMAGE_LEN] = attribute_preimage.try_into().unwrap();
    let preimage_bytes = AttrSlice {
        data: preimage_array,
        len: bv.of_u64::<K_ATTR_INDEX_BITS>(mock.preimage_len),
    };

    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(&mock.raw_buf);
    let digest_bytes = hasher.finalize();

    let expected_digest = bv.from_fn::<256, _>(|idx| {
        let byte_idx = 31 - (idx / 8);
        let bit_idx = idx % 8;
        let byte = digest_bytes[byte_idx];
        let bit_val = (byte.checked_shr(bit_idx as u32).unwrap_or(0) & 1) == 1;
        circuits_boolean::Boolean::new(&l).konst(bit_val)
    });

    let concrete_given = circuits_sha256msg::concrete::ConcreteGiven {
        padded_preimage,
        nblocks,
        length_bytes,
        expected_hash: [0; 8],
    };
    let concrete_derived = circuits_sha256msg::concrete::derived(&concrete_given, 2);
    let sha_derived = circuits_sha256msg::evaluate::evaluate_derived(&concrete_derived, &bv);

    let verifier = AttributeVerifier::new(&l);

    let verifier_args = mdoc_zk_circuits::mso_attribute::circuit::Given {
        attribute_preimage: preimage_bytes,
        field_locator,
        disclosed_attribute: da,
        expected_digest,
    };

    verifier.assert_attribute(&verifier_args, &sha_derived)
}

#[test]
fn test_attribute_success() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    run_attribute_test_mock(&f, &tracker, |_| {}).unwrap();
}

#[test]
fn test_eval_mso_attribute_shared_corruptors() {
    let f = Gf2_128Field::new();
    let corruptors = mso_attribute_corruptors::all_mso_attribute_corruptors();
    for c in corruptors {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            (c.corrupt)(g);
        });
        assert!(
            res.is_err(),
            "Corruptor '{}' failed to cause assertion failure",
            c.name
        );
        let failed = res.failed_paths();
        assert!(
            failed.iter().any(|path| path == &c.expected_path),
            "Corruptor '{}' expected exact failure path '{}', actual failures: {failed:?}",
            c.name,
            c.expected_path
        );
    }
}

fn build_item_mock(name_str: &[u8], cbor_value: &[u8], op: u64) -> MsoAttributeMockGiven {
    let mut map_bytes = Vec::new();
    map_bytes.push(0xa4); // map(4)
    let pos0 = 4 + map_bytes.len() as u64;
    map_bytes.extend_from_slice(b"\x68digestID\x00");
    let len0 = 10;
    let pos1 = 4 + map_bytes.len() as u64;
    map_bytes.extend_from_slice(b"\x66random\x50");
    map_bytes.extend_from_slice(&[0x42u8; 16]);
    let len1 = 24;
    let pos2 = 4 + map_bytes.len() as u64;
    map_bytes.extend_from_slice(b"\x71elementIdentifier");
    let mut cbor_name = vec![0x60 + name_str.len() as u8];
    cbor_name.extend_from_slice(name_str);
    map_bytes.extend_from_slice(&cbor_name);
    let len2 = 18 + cbor_name.len() as u64;
    let pos3 = 4 + map_bytes.len() as u64;
    map_bytes.extend_from_slice(b"\x6celementValue");
    map_bytes.extend_from_slice(cbor_value);
    let len3 = 13 + cbor_value.len() as u64;

    let mut raw_buf = vec![0xd8, 0x18, 0x58, map_bytes.len() as u8];
    raw_buf.extend_from_slice(&map_bytes);
    let preimage_len = raw_buf.len() as u64;

    MsoAttributeMockGiven {
        raw_buf,
        slot_position: [pos0, pos1, pos2, pos3],
        length: [len0, len1, len2, len3],
        permutation: [0, 1, 2, 3],
        disclosed_name: cbor_name.clone(),
        disclosed_name_len: cbor_name.len() as u64,
        disclosed_value: cbor_value.to_vec(),
        disclosed_value_len: cbor_value.len() as u64,
        op,
        preimage_len,
    }
}

#[test]
fn test_attribute_date_comparison_full_date() {
    let f = Gf2_128Field::new();
    let make_full_date = |s: &[u8; 10]| -> Vec<u8> {
        let mut v = vec![0xd9, 0x03, 0xec, 0x6a];
        v.extend_from_slice(s);
        v
    };
    let mdoc_date = make_full_date(b"1971-09-01");
    let eq_date = make_full_date(b"1971-09-01");
    let next_day = make_full_date(b"1971-09-02");
    let prev_day = make_full_date(b"1971-08-31");

    // Le (op = 1): mdoc <= disclosed
    for (disclosed, should_pass) in [(&eq_date, true), (&next_day, true), (&prev_day, false)] {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            *g = build_item_mock(b"birth_date", &mdoc_date, 1);
            g.disclosed_value = disclosed.clone();
            g.disclosed_value_len = disclosed.len() as u64;
        });
        assert_eq!(res.is_ok(), should_pass);
    }

    // Ge (op = 2): mdoc >= disclosed
    for (disclosed, should_pass) in [(&eq_date, true), (&prev_day, true), (&next_day, false)] {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            *g = build_item_mock(b"birth_date", &mdoc_date, 2);
            g.disclosed_value = disclosed.clone();
            g.disclosed_value_len = disclosed.len() as u64;
        });
        assert_eq!(res.is_ok(), should_pass);
    }
}

#[test]
fn test_attribute_date_comparison_tdate() {
    let f = Gf2_128Field::new();
    let make_tdate = |s: &[u8; 20]| -> Vec<u8> {
        let mut v = vec![0xc0, 0x74];
        v.extend_from_slice(s);
        v
    };
    let mdoc_tdate = make_tdate(b"2023-11-15T12:00:00Z");
    let eq_tdate = make_tdate(b"2023-11-15T12:00:00Z");
    let next_sec = make_tdate(b"2023-11-15T12:00:01Z");
    let prev_sec = make_tdate(b"2023-11-15T11:59:59Z");

    // Le (op = 1)
    for (disclosed, should_pass) in [(&eq_tdate, true), (&next_sec, true), (&prev_sec, false)] {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            *g = build_item_mock(b"issue_date", &mdoc_tdate, 1);
            g.disclosed_value = disclosed.clone();
            g.disclosed_value_len = disclosed.len() as u64;
        });
        assert_eq!(res.is_ok(), should_pass);
    }

    // Ge (op = 2)
    for (disclosed, should_pass) in [(&eq_tdate, true), (&prev_sec, true), (&next_sec, false)] {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            *g = build_item_mock(b"issue_date", &mdoc_tdate, 2);
            g.disclosed_value = disclosed.clone();
            g.disclosed_value_len = disclosed.len() as u64;
        });
        assert_eq!(res.is_ok(), should_pass);
    }
}

/// `Le`/`Ge` are only defined when the signed value *and* the threshold are both tagged
/// `full-date`s or both tagged `tdate`s. Mixing the two types, or comparing a tagged date
/// against an untagged text string of the same length (which would otherwise order the same
/// way byte-wise), must trip `cmp_type_ok`.
#[test]
fn test_attribute_date_comparison_rejects_mixed_types() {
    let f = Gf2_128Field::new();
    let full_date = |s: &[u8; 10]| -> Vec<u8> {
        let mut v = vec![0xd9, 0x03, 0xec, 0x6a];
        v.extend_from_slice(s);
        v
    };
    let tdate = |s: &[u8; 20]| -> Vec<u8> {
        let mut v = vec![0xc0, 0x74];
        v.extend_from_slice(s);
        v
    };
    // 14 bytes like a full-date, but a plain `text(13)` without the tag(1004) wrapper.
    let plain14 = {
        let mut v = vec![0x6d];
        v.extend_from_slice(b"1971-09-01xyz");
        v
    };

    let cases: [(&str, Vec<u8>, Vec<u8>, u64); 5] = [
        (
            "full-date item vs tdate threshold (Le)",
            full_date(b"1971-09-01"),
            tdate(b"2000-01-01T00:00:00Z"),
            1,
        ),
        (
            "tdate item vs full-date threshold (Ge)",
            tdate(b"2023-11-15T12:00:00Z"),
            full_date(b"1971-09-01"),
            2,
        ),
        (
            "full-date item vs untagged 14-byte text threshold (Le)",
            full_date(b"1971-09-01"),
            plain14.clone(),
            1,
        ),
        (
            "untagged 14-byte text item vs full-date threshold (Le)",
            plain14.clone(),
            full_date(b"2000-01-01"),
            1,
        ),
        (
            "untagged 14-byte text item vs untagged threshold (Ge)",
            plain14.clone(),
            plain14.clone(),
            2,
        ),
    ];
    for (what, item_value, threshold, op) in &cases {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let res = run_attribute_test_mock(&f, &tracker, |g| {
            *g = build_item_mock(b"birth_date", item_value, *op);
            g.disclosed_value = threshold.clone();
            g.disclosed_value_len = threshold.len() as u64;
        });
        assert!(
            res.is_err(),
            "{what}: mixed-type comparison must be rejected"
        );
        assert!(
            res.failed_paths()
                .iter()
                .any(|p| p == "assert_attribute/assert_item_slot_key_value/cmp_type_ok"),
            "{what}: expected cmp_type_ok to fail, got {:?}",
            res.failed_paths()
        );
    }

    // Control: the untagged value is still fine under `Eq`, which has no type restriction.
    let tracker = compile_logic::tracker::AssertionTracker::new();
    run_attribute_test_mock(&f, &tracker, |g| {
        *g = build_item_mock(b"birth_date", &plain14, 0);
    })
    .unwrap();
}

/// Builds the host-side pseudonym witness for `item_mock` (an `IssuerSignedItem` whose
/// `elementValue` is `58 20 || signed_seed`) when the prover hashes `hashed_seed || context`.
///
/// Honest provers use `hashed_seed == signed_seed`; tests pass a different seed to show
/// that the circuit ties the hashed seed to the signed one (`pnym_seed_copy`).
fn build_pnym_given(
    item_mock: &MsoAttributeMockGiven,
    hashed_seed: &[u8; 32],
    context: &[u8],
) -> PnymConcreteGiven {
    use mdoc_zk_circuits::cbor::{compute_pseudonym, encode_pnym_cbor_value};
    use sha2::{Digest, Sha256};

    let digest = compute_pseudonym(hashed_seed, context);
    let cbor_pnym = encode_pnym_cbor_value(&digest);

    let mut pnym_msg = Vec::with_capacity(hashed_seed.len() + context.len());
    pnym_msg.extend_from_slice(hashed_seed);
    pnym_msg.extend_from_slice(context);
    let (pnym_nblocks, pnym_length_bytes, pnym_padded) =
        circuits_sha256msg::concrete::pad_sha256_message(&pnym_msg, 2).unwrap();

    let item_digest_bytes: [u8; 32] = Sha256::digest(&item_mock.raw_buf).into();
    let expected_digest: [u32; 8] = std::array::from_fn(|i| {
        let chunk: [u8; 4] = item_digest_bytes[4 * i..4 * i + 4].try_into().unwrap();
        u32::from_be_bytes(chunk)
    });

    PnymConcreteGiven {
        name: item_mock.disclosed_name.clone(),
        cbor_value: cbor_pnym,
        context: context.to_vec(),
        preimage: item_mock.raw_buf.clone(),
        field_locator: mdoc_zk_circuits::mso_attribute::concrete::FieldLocator {
            slot_position: item_mock.slot_position.map(|p| p as usize),
            length: item_mock.length.map(|l| l as usize),
            // Identity permutation: logical slot i sits at physical position i.
            permutation: (1 << 2) | (2 << 4) | (3 << 6),
        },
        expected_digest,
        pnym_padded_preimage: pnym_padded,
        pnym_length_bytes: pnym_length_bytes as usize,
        pnym_nblocks,
    }
}

fn run_pnym_mock<'a>(
    f: &'a Gf2_128Field,
    tracker: &'a AssertionTracker,
    given: &PnymConcreteGiven,
    derived: &PnymConcreteDerived,
) -> EvalAssertions<'a> {
    use mdoc_zk_circuits::mso_attribute::pnym::{
        evaluate_derived, evaluate_given, PnymAttributeVerifier,
    };
    let l = EvalLogic::new_with_tracker(f, tracker);
    let bv = BitvecLogic::new(&l);
    let verifier = PnymAttributeVerifier::new(&l);
    let wg = evaluate_given(given, &bv);
    let wd = evaluate_derived(derived, &bv);
    verifier.assert_pnym_attribute(&wg, &wd)
}

/// Asserts that `res` failed and that *every* failed assertion lies under `prefix`
/// (ancestors of `prefix` are tolerated, since `assert_all` nodes may be reported too).
fn assert_fails_only_under(res: &EvalAssertions<'_>, prefix: &str, what: &str) {
    assert!(res.is_err(), "{what}: expected a failure under '{prefix}'");
    let failed = res.failed_paths();
    assert!(
        !failed.is_empty()
            && failed
                .iter()
                .all(|p| p.starts_with(prefix) || prefix.starts_with(p.as_str())),
        "{what}: expected every failed path under '{prefix}', got {failed:?}"
    );
}

fn pnym_seed_item_mock(seed: &[u8; 32]) -> MsoAttributeMockGiven {
    let mut seed_cbor = vec![0x58, 0x20];
    seed_cbor.extend_from_slice(seed);
    // `op` is irrelevant for the pseudonym circuit (it has no operator wire).
    build_item_mock(b"pnym_seed", &seed_cbor, 0)
}

#[test]
fn test_pnym_attribute_verifier() {
    use mdoc_zk_circuits::mso_attribute::pnym::derived as pnym_derived;

    let f = Gf2_128Field::new();
    let seed = [0x55u8; 32];
    let item_mock = pnym_seed_item_mock(&seed);

    for context_len in [1usize, 16, 80] {
        let context: Vec<u8> = (0..context_len)
            .map(|i| (i as u8).wrapping_add(1))
            .collect();
        let base_given = build_pnym_given(&item_mock, &seed, &context);
        let base_derived = pnym_derived(&base_given);

        // 1. Valid passes
        {
            let tracker = AssertionTracker::new();
            run_pnym_mock(&f, &tracker, &base_given, &base_derived).unwrap();
        }

        // 2. Corrupt cbor_value (wrong output hash)
        {
            let mut corrupted = base_given.clone();
            corrupted.cbor_value[5] ^= 1;
            let tracker = AssertionTracker::new();
            let res = run_pnym_mock(&f, &tracker, &corrupted, &base_derived);
            assert!(res.is_err());
            assert!(
                res.failed_paths().iter().any(|p| p.starts_with(
                    "assert_pnym_attribute/assert_pnym_value_and_hash/assert_message_hash/hash_eq"
                )),
                "unexpected failed paths: {:?}",
                res.failed_paths()
            );
        }

        // 3. Corrupt context byte
        {
            let mut corrupted = base_given.clone();
            corrupted.context[0] ^= 1;
            let tracker = AssertionTracker::new();
            let res = run_pnym_mock(&f, &tracker, &corrupted, &base_derived);
            assert!(res.is_err());
            assert!(
                res.failed_paths().iter().any(|p| p.starts_with(
                    "assert_pnym_attribute/assert_pnym_value_and_hash/pnym_context_copy"
                )),
                "unexpected failed paths: {:?}",
                res.failed_paths()
            );
        }

        // 4. Corrupt context_len mismatch
        {
            let mut corrupted = base_given.clone();
            corrupted.pnym_length_bytes += 1;
            let tracker = AssertionTracker::new();
            let res = run_pnym_mock(&f, &tracker, &corrupted, &base_derived);
            assert!(res.is_err());
            assert!(
                res.failed_paths().iter().any(|p| p.starts_with(
                    "assert_pnym_attribute/assert_pnym_value_and_hash/assert_checked_add"
                )),
                "unexpected failed paths: {:?}",
                res.failed_paths()
            );
        }

        // 5. Corrupt disclosed_name != "pnym_seed"
        {
            let mut corrupted = base_given.clone();
            corrupted.name[1] ^= 1;
            let tracker = AssertionTracker::new();
            let res = run_pnym_mock(&f, &tracker, &corrupted, &base_derived);
            assert!(res.is_err());
            assert!(
                res.failed_paths().iter().any(|p| p.starts_with(
                    "assert_pnym_attribute/assert_item_slot_key_value/assert_prefix_equal"
                )),
                "unexpected failed paths: {:?}",
                res.failed_paths()
            );
        }

        // 6. Seed substitution, inconsistent: flip one byte of the hashed seed only.
        {
            let mut corrupted = base_given.clone();
            corrupted.pnym_padded_preimage[0] ^= 1;
            let tracker = AssertionTracker::new();
            let res = run_pnym_mock(&f, &tracker, &corrupted, &base_derived);
            assert!(res.is_err());
            assert!(
                res.failed_paths().iter().any(|p| p.starts_with(
                    "assert_pnym_attribute/assert_pnym_value_and_hash/pnym_seed_copy"
                )),
                "unexpected failed paths: {:?}",
                res.failed_paths()
            );
        }
    }
}

/// The core soundness property of the scheme: a prover who hashes a seed of its own
/// choosing — with a *fully consistent* SHA-256 witness and matching public pseudonym —
/// is still rejected, and rejected precisely by the seed-copy constraint.
#[test]
fn test_pnym_rejects_substituted_seed_with_consistent_hash() {
    use mdoc_zk_circuits::mso_attribute::pnym::derived as pnym_derived;

    let f = Gf2_128Field::new();
    let signed_seed = [0x55u8; 32];
    let item_mock = pnym_seed_item_mock(&signed_seed);
    let context = b"relying-party.example/ctx";

    for other_seed in [[0x66u8; 32], [0x00u8; 32], {
        let mut s = signed_seed;
        s[31] ^= 0x80;
        s
    }] {
        let given = build_pnym_given(&item_mock, &other_seed, context);
        let derived = pnym_derived(&given);
        let tracker = AssertionTracker::new();
        let res = run_pnym_mock(&f, &tracker, &given, &derived);
        assert_fails_only_under(
            &res,
            "assert_pnym_attribute/assert_pnym_value_and_hash/pnym_seed_copy",
            "substituted seed",
        );
    }

    // Control: the honest witness for the same item and context passes.
    let given = build_pnym_given(&item_mock, &signed_seed, context);
    let derived = pnym_derived(&given);
    let tracker = AssertionTracker::new();
    run_pnym_mock(&f, &tracker, &given, &derived).unwrap();
}

/// `1 <= context.len <= K_PNYM_CONTEXT_MAX` is enforced in-circuit on the public input, not
/// only by the runtime. With an otherwise fully consistent witness the bounds check must be
/// the *only* failing assertion.
#[test]
fn test_pnym_context_length_bounds() {
    use mdoc_zk_circuits::mso_attribute::{
        constants::K_PNYM_CONTEXT_MAX, pnym::derived as pnym_derived,
    };

    let f = Gf2_128Field::new();
    let seed = [0x55u8; 32];
    let item_mock = pnym_seed_item_mock(&seed);

    for (context_len, should_pass) in [
        (0usize, false),
        (1, true),
        (K_PNYM_CONTEXT_MAX, true),
        (K_PNYM_CONTEXT_MAX + 1, false),
    ] {
        let context: Vec<u8> = (0..context_len).map(|i| 0xA0 ^ (i as u8)).collect();
        let given = build_pnym_given(&item_mock, &seed, &context);
        let derived = pnym_derived(&given);
        let tracker = AssertionTracker::new();
        let res = run_pnym_mock(&f, &tracker, &given, &derived);
        if should_pass {
            assert!(
                res.is_ok(),
                "context_len={context_len}: {:?}",
                res.failed_paths()
            );
        } else {
            assert_fails_only_under(
                &res,
                "assert_pnym_attribute/assert_pnym_value_and_hash/pnym_context_len_bounds",
                &format!("context_len={context_len}"),
            );
        }
    }
}

fn run_large_attribute_test_mock<'a>(
    f: &'a Gf2_128Field,
    tracker: &'a AssertionTracker,
    mock: &MsoAttributeMockGiven,
) -> EvalAssertions<'a> {
    use mdoc_zk_circuits::mso_attribute::constants::{
        K_LARGE_ATTR_PREIMAGE_LEN, K_LARGE_ATTR_SHA_BLOCKS, K_LARGE_ATTR_VAL_LEN,
    };
    use sha2::{Digest, Sha256};

    let l = EvalLogic::new_with_tracker(f, tracker);
    let bv = BitvecLogic::new(&l);

    let (nblocks, length_bytes, padded_preimage) =
        circuits_sha256msg::concrete::pad_sha256_message(&mock.raw_buf, K_LARGE_ATTR_SHA_BLOCKS)
            .unwrap();
    assert_eq!(padded_preimage.len(), K_LARGE_ATTR_PREIMAGE_LEN);
    let attribute_preimage: Vec<_> = padded_preimage.iter().map(|&b| bv.of_u8(b)).collect();
    let preimage_len = bv.of_u64::<K_ATTR_INDEX_BITS>(mock.preimage_len);

    let zero_v8 = bv.of_u8(0);
    let mut oa_attr = [(); 32].map(|_| zero_v8.clone());
    for (slot, &b) in oa_attr.iter_mut().zip(mock.disclosed_name.iter().take(32)) {
        *slot = bv.of_u8(b);
    }
    let expected_name = AttrSlice {
        data: oa_attr,
        len: bv.of_u64::<K_ATTR_INDEX_BITS>(mock.disclosed_name_len),
    };

    let mut oa_v1 = vec![zero_v8; K_LARGE_ATTR_VAL_LEN];
    for (slot, &b) in oa_v1
        .iter_mut()
        .zip(mock.disclosed_value.iter().take(K_LARGE_ATTR_VAL_LEN))
    {
        *slot = bv.of_u8(b);
    }
    let expected_cbor_value_len = bv.of_u64::<K_ATTR_INDEX_BITS>(mock.disclosed_value_len);
    let op = bv.of_u64::<2>(mock.op);

    let field_locator = FieldLocator {
        slot_position: std::array::from_fn(|i| {
            bv.of_u64::<K_ATTR_INDEX_BITS>(mock.slot_position[i])
        }),
        length: std::array::from_fn(|i| bv.of_u64::<K_ATTR_INDEX_BITS>(mock.length[i])),
        permutation: std::array::from_fn(|i| bv.of_u64::<2>(mock.permutation[i])),
    };

    let digest_bytes = Sha256::digest(&mock.raw_buf);
    let expected_digest = bv.from_fn::<256, _>(|idx| {
        let byte_idx = 31 - (idx / 8);
        let bit_idx = idx % 8;
        let byte = digest_bytes[byte_idx];
        let bit_val = ((byte >> bit_idx) & 1) == 1;
        circuits_boolean::Boolean::new(&l).konst(bit_val)
    });

    let concrete_given = circuits_sha256msg::concrete::ConcreteGiven {
        padded_preimage,
        nblocks,
        length_bytes,
        expected_hash: [0; 8],
    };
    let concrete_derived =
        circuits_sha256msg::concrete::derived(&concrete_given, K_LARGE_ATTR_SHA_BLOCKS);
    let sha_derived = circuits_sha256msg::evaluate::evaluate_derived(&concrete_derived, &bv);

    let verifier =
        AttributeVerifier::<_, K_LARGE_ATTR_SHA_BLOCKS, K_LARGE_ATTR_VAL_LEN>::with_size(&l);
    verifier.assert_attribute_slices(
        &attribute_preimage,
        &preimage_len,
        &field_locator,
        &expected_name,
        &oa_v1,
        &expected_cbor_value_len,
        &op,
        &expected_digest,
        &sha_derived,
    )
}

#[test]
fn test_large_attribute_verifier_190b_and_20b() {
    let f = Gf2_128Field::new();

    // 1. 190-byte IssuerSignedItemBytes (4 SHA-256 blocks: 190 + 9 = 199 bytes > 192 bytes):
    //    70-byte fixed CBOR framing + 11-byte cbor_id (b"\x6alarge_190b") + 109-byte cbor_value = 190 bytes.
    let mut val_109b = vec![0x58, 0x6b]; // bstr(107) -> 109 CBOR bytes
    val_109b.extend((0..107u8).map(|i| i.wrapping_mul(5).wrapping_add(3)));
    let mock_190b = build_item_mock(b"large_190b", &val_109b, 0);
    assert_eq!(mock_190b.raw_buf.len(), 190);
    assert_eq!(mock_190b.preimage_len, 190);

    let tracker = AssertionTracker::new();
    run_large_attribute_test_mock(&f, &tracker, &mock_190b).unwrap();

    // Tampering with byte 100 (> 64) of the 190-byte item's value must fail
    let mut bad_190b = mock_190b.clone();
    bad_190b.disclosed_value[100] ^= 0x01;
    let tracker = AssertionTracker::new();
    let res_bad_190b = run_large_attribute_test_mock(&f, &tracker, &bad_190b);
    assert!(res_bad_190b.is_err());

    // 2. 20-byte attribute value (bstr(19) -> 20 CBOR bytes, 101-byte IssuerSignedItemBytes = 2 SHA-256 blocks)
    //    verified through the 4-block large AttributeVerifier:
    let mut val_20b = vec![0x53]; // bstr(19) -> 20 CBOR bytes
    val_20b.extend((0..19u8).map(|i| i.wrapping_add(0x20)));
    assert_eq!(val_20b.len(), 20);
    let mock_20b = build_item_mock(b"small_20b_", &val_20b, 0);
    assert_eq!(mock_20b.disclosed_value.len(), 20);

    let tracker = AssertionTracker::new();
    run_large_attribute_test_mock(&f, &tracker, &mock_20b).unwrap();

    // Tampering with the 20-byte attribute value must fail
    let mut bad_20b = mock_20b.clone();
    bad_20b.disclosed_value[19] ^= 0x01;
    let tracker = AssertionTracker::new();
    let res_bad_20b = run_large_attribute_test_mock(&f, &tracker, &bad_20b);
    assert!(res_bad_20b.is_err());
}
