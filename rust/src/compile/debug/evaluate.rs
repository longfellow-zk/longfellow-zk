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

//! Name the outcome of a reference evaluation by the compiled assertions.
//!
//! `core::proto::v2::evaluate` reports which terms and outputs failed; this
//! maps them through the compiler's debug symbols to assertion statuses.

use super::{CircuitDebugSymbols, CompiledEvalAssertions, WireRef};
use crate::{
    compile::logic::{AssertionMap, AssertionStatus},
    core::{
        algebra::{AlgebraicField, ElementOf, SerializableField},
        proto::v2::{
            evaluate::{convert, evaluate, EvalError},
            Circuit,
        },
    },
};

fn eval_circuit<'a, F: AlgebraicField + SerializableField>(
    f: &F,
    circuit: &Circuit<F>,
    symbols: &'a CircuitDebugSymbols,
    inputs: &[ElementOf<F>],
) -> CompiledEvalAssertions<'a, EvalError> {
    let tracker = symbols.tracker();
    let evaluation = match evaluate(f, circuit, inputs) {
        Ok(evaluation) => evaluation,
        Err(err) => {
            return CompiledEvalAssertions {
                result: Err(err),
                fates: AssertionMap::new(),
                tracker,
            };
        }
    };
    let mut fates = AssertionMap::new();
    let mut failed = !evaluation.failed_terms.is_empty();
    for &(layer, index) in &evaluation.failed_terms {
        if let Some(id) = symbols.get_id(&WireRef::new(layer, index)) {
            fates.insert(
                tracker,
                id,
                AssertionStatus::Failed("layer assertion failed".to_string()),
            );
        }
    }
    for (i, y) in evaluation.outputs.iter().enumerate() {
        let is_zero = f.is_zero(y);
        failed |= !is_zero;
        if let Some(id) = symbols.get_id(&WireRef::new(0, i)) {
            let status = if is_zero {
                AssertionStatus::Passed
            } else {
                AssertionStatus::Failed("circuit output non-zero".to_string())
            };
            fates.insert_if_absent(tracker, id, status);
        }
    }
    CompiledEvalAssertions {
        result: if failed {
            Err(EvalError::AssertionFailure)
        } else {
            Ok(())
        },
        fates,
        tracker,
    }
}

/// Evaluate a circuit compiled over `fc` in the field `fr`, after re-encoding
/// it through the circuit format.
pub(crate) fn eval_circuit_fc<'a, FC: SerializableField, FR: AlgebraicField + SerializableField>(
    fc: &FC,
    fr: &FR,
    circuit: &Circuit<FC>,
    symbols: &'a CircuitDebugSymbols,
    inputs: &[ElementOf<FR>],
) -> Result<CompiledEvalAssertions<'a, EvalError>, String> {
    let converted = convert(fc, fr, circuit)?;
    Ok(eval_circuit(fr, &converted, symbols, inputs))
}
