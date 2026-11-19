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

use crate::{
    compile::{
        algebra::{gf2_128::Gf2_128Field, CompileField},
        logic::{AssertionScope, EvalContext, EvalLogic, EvalWire, Logic},
    },
    core::algebra::SupportsU64Conversions,
};

fn run_test_eval_logic<F: CompileField + SupportsU64Conversions>(field: &F) {
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(field, &tracker);
    let z = l.zero();
    let o = l.one();
    assert_eq!(z.value, field.zero());
    assert_eq!(o.value, field.one());

    let two = l.add(&o, &o);
    assert_eq!(l.to_stringw_debug(&two), "Gf2_128(0)");

    let three = l.konst(&field.u64_to_element(3));
    assert_eq!(three.value, field.u64_to_element(3));

    let three_field = l.konst(&field.u64_to_element(3));
    let expected = format!("{:?}", field.u64_to_element(3));
    assert_eq!(l.to_stringw_debug(&three_field), expected);

    let neg_one = field.mone();
    assert_eq!(neg_one, field.one());

    let assert_z = l.assert0("assert_z", &z);
    assert!(tracker.is_ok(&assert_z.all_items()));
}

#[test]
fn test_eval_logic() {
    let field = Gf2_128Field::new();
    run_test_eval_logic(&field);
}

fn run_test_eval_assert0_panic<F: CompileField>(field: &F) {
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(field, &tracker);
    let o = l.one();
    let assert_o = l.assert0("assert_o", &o);
    assert!(tracker.is_err(&assert_o.all_items()));
}

#[test]
fn test_eval_assert0_panic() {
    let field = Gf2_128Field::new();
    run_test_eval_assert0_panic(&field);
}

#[test]
fn test_eval_guarded_assertions() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(&field, &tracker);
    let zero = logic.zero();
    let one = logic.one();

    let value = logic.with_assertions(logic.assert0("dependency", &one), &one);
    let assertions = logic.assert0("value", &value);
    logic.assert_when(&zero, assertions.clone()).unwrap();
    let enabled = logic.assert_when(&one, assertions.clone());
    assert_eq!(enabled.failed_paths(), ["dependency", "value"]);

    let guard = logic.with_assertions(logic.assert0("guard_dependency", &one), &zero);
    let disabled = logic.assert_when(&guard, assertions);
    assert_eq!(disabled.failed_paths(), ["guard_dependency"]);
}

fn run_test_eval_with_assertions_propagation<F: CompileField>(field: &F) {
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(field, &tracker);

    let one = l.one();
    let zero = l.zero();

    // 1. A valid assertion (zero == zero) should propagate Ok
    let ok_assertion = l.assert0("assert_zero", &zero);
    let val_ok = l.with_assertions(ok_assertion, &one);
    assert!(tracker.is_ok(&val_ok.assertions));

    // 2. An invalid attached assertion marks the wire invalid, while its
    // provenance remains distinct from computation errors.
    let err_assertion = l.assert0("assert_one", &one);
    let val_err = l.with_assertions(err_assertion, &one);
    assert!(tracker.is_err(&val_err.assertions));

    // 3. Test exact assertion propagation through all logic operations.
    let assert_propagated = |wire: EvalWire<F>| {
        assert!(tracker.is_err(&wire.assertions));
        let result = l.assert0("consumer", &wire);
        tracker.assert_any_failed_at("assert_one", &result.all_items());
    };

    assert_propagated(l.precious(&val_err));
    assert_propagated(l.neg(&val_err));

    assert_propagated(l.add(&val_err, &zero));
    assert_propagated(l.add(&zero, &val_err));

    assert_propagated(l.sub(&val_err, &zero));
    assert_propagated(l.sub(&zero, &val_err));

    assert_propagated(l.mul(&val_err, &zero));
    assert_propagated(l.mul(&zero, &val_err));

    assert_propagated(l.mulk(&field.one(), &val_err));

    assert_propagated(l.quadratic(&field.one(), &val_err, &zero));
    assert_propagated(l.quadratic(&field.one(), &zero, &val_err));

    assert_propagated(l.sum(&[zero.clone(), val_err.clone(), zero.clone()]));

    assert_propagated(l.with_assertions(l.ok(), &val_err));

    let newly_attached = l.with_assertions(l.assert0("check_one", &one), &zero);
    let result = l.assert0("consumer", &newly_attached);
    assert_eq!(tracker.failed_paths(&result.all_items()), vec!["check_one"]);
    assert_eq!(tracker.passed_paths(&result.all_items()), vec!["consumer"]);
}

#[test]
fn test_eval_with_assertions_propagation() {
    let field = Gf2_128Field::new();
    run_test_eval_with_assertions_propagation(&field);
}

#[test]
fn test_eval_assertion_dag_paths() {
    let field = Gf2_128Field::new();
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(&field, &tracker);

    let z = l.zero();
    let o = l.one();

    let leaf1 = l.assert0("check_zero1", &z);
    let leaf2 = l.assert0("check_non_zero", &z);
    let leaf3 = l.assert0("check_one", &o);

    let inner = l.assert_all("inner_block", &[leaf1, leaf2]);
    let outer = l.assert_all("outer_block", &[inner, leaf3]);

    let path_strings = tracker.all_paths(&outer.all_items());
    assert_eq!(
        path_strings,
        vec![
            "outer_block/inner_block/check_zero1",
            "outer_block/inner_block/check_non_zero",
            "outer_block/check_one"
        ]
    );
}

#[test]
fn test_eval_assert_mapi() {
    let field = Gf2_128Field::new();
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(&field, &tracker);
    let z = l.zero();

    let mapi_assertion = l.assert_mapi("loop_check", 0..3, |_i| l.assert0("check", &z));
    let mapi_paths = tracker.all_paths(&mapi_assertion.all_items());
    assert_eq!(
        mapi_paths,
        vec![
            "loop_check/loop_check.0/check",
            "loop_check/loop_check.1/check",
            "loop_check/loop_check.2/check"
        ]
    );
}

#[test]
fn test_eval_assertion_status_tracking() {
    let field = Gf2_128Field::new();
    type L<'a, F> = EvalLogic<'a, F>;
    let tracker = AssertionScope::new();
    let l = L::new(&field, &tracker);
    let z = l.zero();
    let o = l.one();

    let pass_a = l.assert0("good_zero", &z);
    let fail_a = l.assert0("bad_zero", &o);

    let combined = l.assert_all("top", &[pass_a, fail_a]);

    assert!(tracker.is_err(&combined.all_items()));
    assert_eq!(
        tracker.passed_paths(&combined.all_items()),
        vec!["top/good_zero"]
    );
    assert_eq!(
        tracker.failed_paths(&combined.all_items()),
        vec!["top/bad_zero"]
    );

    tracker.assert_any_failed_at("top/bad_zero", &combined.all_items());
    tracker.assert_all_passed_at("top/good_zero", &combined.all_items());
}

#[test]
fn test_eval_attached_assertion_keeps_exact_scoped_path() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(&field, &tracker);
    let computed = l.one();
    let witness = l.zero();

    let sliced = l.slicing("slice", &witness, &computed);
    let consumer = l.assert0("consumer", &sliced);
    let root = l.assert_all("root", &[consumer]);

    assert_eq!(
        tracker.all_paths(&root.all_items()),
        vec!["slice", "root/consumer"]
    );
    assert_eq!(tracker.failed_paths(&root.all_items()), vec!["slice"]);
    assert_eq!(
        tracker.passed_paths(&root.all_items()),
        vec!["root/consumer"]
    );
}

#[test]
fn test_eval_shared_attached_assertion_is_reported_once() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(&field, &tracker);
    let bad = l.assert0("attached", &l.one());
    let wire = l.with_assertions(bad, &l.zero());

    let diamond = l.add(&wire, &wire);
    let result = l.assert0("consumer", &diamond);

    assert_eq!(tracker.failed_paths(&result.all_items()), vec!["attached"]);
    assert_eq!(tracker.passed_paths(&result.all_items()), vec!["consumer"]);
}

#[test]
fn test_eval_distinct_assertions_with_the_same_path_remain_distinct() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(&field, &tracker);
    let left = l.with_assertions(l.assert0("same", &l.one()), &l.zero());
    let right = l.with_assertions(l.assert0("same", &l.one()), &l.zero());

    let result = l.assert0("consumer", &l.add(&left, &right));

    assert_eq!(
        tracker.failed_paths(&result.all_items()),
        vec!["same", "same"]
    );
    assert_eq!(tracker.passed_paths(&result.all_items()), vec!["consumer"]);
}

#[test]
fn test_eval_union_reports_failure_from_any_alias() {
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(&field, &tracker);
    let passed = l.assert0("passed", &l.zero());
    let failed = l.assert0("failed", &l.one());
    let passed_id = passed.all_items().ids().next().unwrap();
    let failed_id = failed.all_items().ids().next().unwrap();
    tracker.union(passed_id, failed_id);

    let fates = passed.all_items().merged(&failed.all_items());

    // Both aliases report the group's failure.
    assert_eq!(tracker.failed_paths(&fates), vec!["passed", "failed"]);
    assert!(tracker.passed_paths(&fates).is_empty());
    assert!(!tracker.is_ok(&fates));
}

#[test]
#[should_panic(expected = "assertions from different evaluator scopes cannot be queried")]
fn test_scope_rejects_queries_about_another_scope() {
    // Assertion IDs are local to a scope, so another scope would resolve them
    // to its own, unrelated paths.
    let field = Gf2_128Field::new();
    let (scope_a, scope_b) = (AssertionScope::new(), AssertionScope::new());
    let a = EvalLogic::new(&field, &scope_a);
    let failed = a.assert0("failed_in_a", &a.one());
    scope_b.failed_paths(&failed.all_items());
}

#[test]
fn test_eval_context_owns_tracker() {
    let field = Gf2_128Field::new();
    let context = EvalContext::new(&field);
    let result = context.run(|logic| logic.assert0("zero", &logic.zero()));
    result.assert_all_passed();
}

#[test]
#[should_panic(expected = "assertions from different evaluator scopes cannot be combined")]
fn test_eval_rejects_assertions_from_another_scope() {
    // Assertion IDs are local to a scope: before ownership was checked, the
    // pass in `b` overwrote the failure in `a` and the combination passed.
    let field = Gf2_128Field::new();
    let (scope_a, scope_b) = (AssertionScope::new(), AssertionScope::new());
    let a = EvalLogic::new(&field, &scope_a);
    let b = EvalLogic::new(&field, &scope_b);
    let failed = a.assert0("failed_in_a", &a.one());
    let passed = b.assert0("passed_in_b", &b.zero());
    assert!(failed.is_err() && passed.is_ok());
    a.assert_all("combined", &[failed, passed]);
}

#[test]
#[should_panic(expected = "assertions from different evaluator scopes cannot be combined")]
fn test_eval_rejects_wires_from_another_scope() {
    let field = Gf2_128Field::new();
    let (scope_a, scope_b) = (AssertionScope::new(), AssertionScope::new());
    let a = EvalLogic::new(&field, &scope_a);
    let b = EvalLogic::new(&field, &scope_b);
    let checked = a.assert0("checked_in_a", &a.zero());
    let wire = a.with_assertions(checked, &a.one());
    b.add(&wire, &b.one());
}

#[test]
#[should_panic(
    expected = "Expected assertion failure at 'expected', but actual failed assertion paths were: [\"unrelated\"]"
)]
fn test_assert_any_failed_at_rejects_a_passing_expected_path() {
    use crate::compile::logic::{AssertionMap, AssertionStatus};
    // An unrelated failure must not satisfy a check for a failure elsewhere,
    // and the message names the failures that did occur.
    let tracker = AssertionScope::new();
    let expected = tracker.new_leaf("expected");
    let unrelated = tracker.new_leaf("unrelated");
    let mut fates = AssertionMap::new();
    fates.insert(&tracker, expected, AssertionStatus::Passed);
    fates.insert(
        &tracker,
        unrelated,
        AssertionStatus::Failed("unrelated".to_string()),
    );
    tracker.assert_any_failed_at("expected", &fates);
}
