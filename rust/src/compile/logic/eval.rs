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

//! Direct evaluation of circuit logic with exact assertion provenance.

use crate::{
    compile::{
        algebra::CompileField,
        logic::{AssertionMap, AssertionScope, AssertionStatus, Logic, LogicIO},
    },
    core::algebra::ElementOf,
};

pub(crate) struct EvalWire<F: CompileField> {
    pub(crate) value: ElementOf<F>,
    pub(crate) assertions: AssertionMap,
}

impl<F: CompileField> Clone for EvalWire<F> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            assertions: self.assertions.clone(),
        }
    }
}

impl<F: CompileField> EvalWire<F> {
    fn new(value: ElementOf<F>, assertions: AssertionMap) -> Self {
        Self { value, assertions }
    }
}

impl<F: CompileField> PartialEq for EvalWire<F> {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<F: CompileField> Eq for EvalWire<F> {}

impl<F: CompileField> std::fmt::Debug for EvalWire<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EvalWire")
            .field("value", &self.value)
            .field("has_attached_assertions", &!self.assertions.is_empty())
            .finish()
    }
}

pub(crate) struct EvalLogic<'a, F: CompileField> {
    f: &'a F,
    tracker: &'a AssertionScope,
}

/// Owns the assertion scope for one direct-evaluation session.
pub(crate) struct EvalContext<'a, F: CompileField> {
    f: &'a F,
    tracker: AssertionScope,
}

impl<'a, F: CompileField> EvalContext<'a, F> {
    pub(crate) fn new(f: &'a F) -> Self {
        Self {
            f,
            tracker: AssertionScope::new(),
        }
    }

    pub(crate) fn run<'ctx>(
        &'ctx self,
        build: impl FnOnce(&EvalLogic<'ctx, F>) -> EvalAssertions<'ctx>,
    ) -> EvalAssertions<'ctx> {
        let logic = EvalLogic::new(self.f, &self.tracker);
        let result = build(&logic);
        assert!(
            std::ptr::eq(result.tracker, &self.tracker),
            "assertions from different evaluator scopes cannot be combined"
        );
        logic.result(result.scoped, result.unscoped)
    }
}

impl<'a, F: CompileField> EvalLogic<'a, F> {
    pub(crate) fn new(f: &'a F, tracker: &'a AssertionScope) -> Self {
        Self { f, tracker }
    }

    pub(crate) fn new_with_tracker(f: &'a F, tracker: &'a AssertionScope) -> Self {
        Self::new(f, tracker)
    }

    // Every wire and assertion set this logic produces passes through `wire` or
    // `result`, which reject assertions issued by another scope. Operations
    // that record state in the scope check their inputs first.
    fn wire(&self, value: ElementOf<F>, assertions: AssertionMap) -> EvalWire<F> {
        assertions.check_owner(self.tracker, "combined");
        EvalWire::new(value, assertions)
    }

    fn combine(&self, x: &EvalWire<F>, y: &EvalWire<F>, value: ElementOf<F>) -> EvalWire<F> {
        let assertions = x.assertions.merged(&y.assertions);
        self.wire(value, assertions)
    }

    fn result(&self, scoped: AssertionMap, unscoped: AssertionMap) -> EvalAssertions<'a> {
        scoped.check_owner(self.tracker, "combined");
        unscoped.check_owner(self.tracker, "combined");
        EvalAssertions {
            scoped,
            unscoped,
            tracker: self.tracker,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct EvalAssertions<'a> {
    pub(crate) scoped: AssertionMap,
    pub(crate) unscoped: AssertionMap,
    pub(crate) tracker: &'a AssertionScope,
}

impl<'a> EvalAssertions<'a> {
    pub(crate) fn all_items(&self) -> AssertionMap {
        self.scoped.merged(&self.unscoped)
    }

    pub(crate) fn is_ok(&self) -> bool {
        self.tracker.is_ok(&self.all_items())
    }

    pub(crate) fn is_err(&self) -> bool {
        self.tracker.is_err(&self.all_items())
    }

    pub(crate) fn unwrap(self) {
        self.assert_all_passed();
    }

    pub(crate) fn failed_paths(&self) -> Vec<String> {
        self.tracker.failed_paths(&self.all_items())
    }

    pub(crate) fn assert_all_passed(&self) {
        self.tracker.assert_all_passed(&self.all_items());
    }

    pub(crate) fn assert_any_failed_at(&self, expected_path: &str) {
        self.tracker
            .assert_any_failed_at(expected_path, &self.all_items());
    }
}

impl<'a, F: CompileField> Logic for EvalLogic<'a, F> {
    type F = F;
    type Wire = EvalWire<F>;
    type Assertions = EvalAssertions<'a>;

    fn field(&self) -> &Self::F {
        self.f
    }

    fn zero(&self) -> Self::Wire {
        self.wire(self.f.zero(), AssertionMap::new())
    }

    fn one(&self) -> Self::Wire {
        self.wire(self.f.one(), AssertionMap::new())
    }

    fn konst(&self, x: &ElementOf<F>) -> Self::Wire {
        self.wire(x.clone(), AssertionMap::new())
    }

    fn precious(&self, x: &Self::Wire) -> Self::Wire {
        self.wire(x.value.clone(), x.assertions.clone())
    }

    fn sum(&self, xs: &[Self::Wire]) -> Self::Wire {
        let mut val = self.f.zero();
        let mut assertions = AssertionMap::new();
        for x in xs {
            val = self.f.addf(&val, &x.value);
            assertions = assertions.merged(&x.assertions);
        }
        self.wire(val, assertions)
    }

    fn neg(&self, x: &Self::Wire) -> Self::Wire {
        self.wire(self.f.neg(&x.value), x.assertions.clone())
    }

    fn add(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.combine(x, y, self.f.addf(&x.value, &y.value))
    }

    fn sub(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.combine(x, y, self.f.subf(&x.value, &y.value))
    }

    fn mul(&self, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.combine(x, y, self.f.mulf(&x.value, &y.value))
    }

    fn mulk(&self, e: &ElementOf<F>, y: &Self::Wire) -> Self::Wire {
        self.wire(self.f.mulf(e, &y.value), y.assertions.clone())
    }

    fn quadratic(&self, e: &ElementOf<F>, x: &Self::Wire, y: &Self::Wire) -> Self::Wire {
        self.combine(x, y, self.f.mulf(e, &self.f.mulf(&x.value, &y.value)))
    }

    fn ok(&self) -> Self::Assertions {
        self.result(AssertionMap::new(), AssertionMap::new())
    }

    fn assert0(&self, name: &str, x: &Self::Wire) -> Self::Assertions {
        assert!(!name.is_empty(), "assert0 requires a non-empty name");
        x.assertions.check_owner(self.tracker, "combined");
        let status = if x.value.eq(&self.f.zero()) {
            AssertionStatus::Passed
        } else {
            AssertionStatus::Failed(format!("expected zero, got {:?}", x.value))
        };
        let id = self.tracker.new_leaf(name);
        let mut scoped = AssertionMap::new();
        scoped.insert(self.tracker, id, status);
        self.result(scoped, x.assertions.clone())
    }

    fn assert_all(&self, name: &str, assertions: &[Self::Assertions]) -> Self::Assertions {
        assert!(!name.is_empty(), "assert_all requires a non-empty name");
        let mut scoped = AssertionMap::new();
        let mut unscoped = AssertionMap::new();
        for a in assertions {
            scoped = scoped.merged(&a.scoped);
            unscoped = unscoped.merged(&a.unscoped);
        }
        // Check ownership before renaming the scope's assertions.
        scoped.check_owner(self.tracker, "combined");
        unscoped.check_owner(self.tracker, "combined");
        for id in scoped.ids() {
            self.tracker.prepend_scope(id, name);
        }
        self.result(scoped, unscoped)
    }

    fn with_assertions(&self, assertions: Self::Assertions, x: &Self::Wire) -> Self::Wire {
        let attached = assertions.scoped.merged(&assertions.unscoped);
        let new_unscoped = x.assertions.merged(&attached);
        self.wire(x.value.clone(), new_unscoped)
    }

    fn to_stringw_debug(&self, x: &Self::Wire) -> String {
        format!("{:?}", x.value)
    }
}

impl<F: CompileField> LogicIO for EvalLogic<'_, F> {
    fn input(&self, _position_in_input_array: usize) -> Self::Wire {
        panic!("input is not supported in EvalLogic");
    }

    fn position_in_input_array(&self, _x: &Self::Wire) -> usize {
        panic!("position_in_input_array is not supported in EvalLogic");
    }
}

impl<F: CompileField> std::fmt::Debug for EvalLogic<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EvalLogic").finish()
    }
}
