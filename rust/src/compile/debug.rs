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

//! Debug symbol definitions and evaluation assertion types for compiled circuits.

/// Reference to a specific wire index within a circuit layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WireRef {
    /// Layer index (e.g. 0 for circuit output layer).
    pub layer: usize,
    /// Wire index within the specified layer.
    pub index: usize,
}

impl WireRef {
    /// Creates a new wire reference at `(layer, index)`.
    pub fn new(layer: usize, index: usize) -> Self {
        Self { layer, index }
    }
}

use crate::compile::logic::{AssertionId, AssertionMap, AssertionScope};

/// Mapping from a specific circuit output wire to its assertion ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertionSymbol {
    /// Target wire reference in the compiled circuit.
    pub wire: WireRef,
    /// Assertion ID tracked in AssertionScope.
    pub id: AssertionId,
}

impl AssertionSymbol {
    /// Creates a new assertion symbol pairing a wire reference with an assertion ID.
    pub fn new(wire: WireRef, id: AssertionId) -> Self {
        Self { wire, id }
    }
}

/// Collection of debug symbols associated with a compiled circuit.
#[derive(Debug, Default)]
pub struct CircuitDebugSymbols {
    /// List of assertion symbols for output wires.
    symbols: Vec<AssertionSymbol>,
    /// Associated assertion scope.
    tracker: AssertionScope,
}

impl CircuitDebugSymbols {
    /// Creates a new container of circuit debug symbols.
    pub fn new(symbols: Vec<AssertionSymbol>, tracker: AssertionScope) -> Self {
        Self { symbols, tracker }
    }

    /// Returns the number of assertion symbols.
    pub fn assertion_count(&self) -> usize {
        self.symbols.len()
    }

    /// Returns all assertion symbols recorded for this circuit.
    pub fn assertion_symbols(&self) -> &[AssertionSymbol] {
        &self.symbols
    }

    /// Returns the tracker path for an assertion identifier, if any.
    pub fn get_path(&self, id: AssertionId) -> Option<String> {
        if id.is_nil() {
            return None;
        }
        let path = self.tracker.get_path(id);
        (!path.is_empty()).then_some(path)
    }

    /// Looks up the assertion symbol for a given wire reference.
    pub fn get_symbol(&self, wire: &WireRef) -> Option<&AssertionSymbol> {
        self.symbols.iter().find(|s| &s.wire == wire)
    }

    /// Looks up the assertion ID for a given wire reference.
    pub fn get_id(&self, wire: &WireRef) -> Option<AssertionId> {
        self.get_symbol(wire).map(|s| s.id)
    }

    /// Looks up the assertion symbol by path.
    pub fn get_symbol_by_path(&self, path: &str) -> Option<&AssertionSymbol> {
        self.symbols
            .iter()
            .find(|symbol| self.get_path(symbol.id).as_deref() == Some(path))
    }

    pub fn tracker(&self) -> &AssertionScope {
        &self.tracker
    }
}

/// Aggregate result of evaluating a compiled circuit, detailing overall pass/fail status and
/// per-assertion evaluation.
#[derive(Clone)]
pub struct CompiledEvalAssertions<'a, E = String> {
    /// Overall result of the circuit evaluation.
    pub result: Result<(), E>,
    /// Status of each evaluated assertion, owned by `tracker`.
    pub fates: AssertionMap,
    /// Reference to the assertion scope.
    pub tracker: &'a AssertionScope,
}

impl<'a, E: std::fmt::Debug> CompiledEvalAssertions<'a, E> {
    /// Returns `true` if the overall evaluation succeeded.
    pub fn is_ok(&self) -> bool {
        self.result.is_ok() && self.tracker.is_ok(&self.fates)
    }

    /// Returns `true` if the overall evaluation failed.
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    /// Returns a list of formatted paths for assertions that failed.
    pub fn failed_paths(&self) -> Vec<String> {
        self.tracker.failed_paths(&self.fates)
    }

    /// Asserts that all evaluations passed, panicking with details if any failed.
    pub fn assert_all_passed(&self) {
        self.tracker.assert_all_passed(&self.fates);
    }

    /// Asserts that at least one assertion failed at exactly `expected_path`.
    pub fn assert_any_failed_at(&self, expected_path: &str) {
        self.tracker
            .assert_any_failed_at(expected_path, &self.fates);
    }
}

#[cfg(test)]
pub(crate) mod evaluate;
