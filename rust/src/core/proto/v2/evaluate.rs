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

//! Reference evaluation of a v2 circuit, for tests.
//!
//! The evaluator states what a circuit in this format computes, over any field
//! with the core arithmetic traits, so tests can run a compiled circuit in
//! either the compile-time or the run-time field. A quadratic or linear term
//! whose coefficient is zero is an assertion that its product or input is
//! zero; every output wire is an assertion that it evaluates to zero.

use crate::core::{
    algebra::{AlgebraicField, ElementOf, SerializableField},
    proto::v2::{
        classify_constants, Circuit, CircuitReader, CircuitWriter, CoefficientClass, Layer,
    },
};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum EvalError {
    AssertionFailure,
    InputSizeMismatch { expected: usize, got: usize },
}

/// The outcome of evaluating a circuit on one input vector.
pub(crate) struct Evaluation<E> {
    /// `(layer, wire)` of every term asserting zero that did not hold, in
    /// layer order; layer 0 is the output layer.
    pub(crate) failed_terms: Vec<(usize, usize)>,
    /// The output values; each must be zero.
    pub(crate) outputs: Vec<E>,
}

/// An empty input vector, to be filled by the caller.
pub(crate) fn initial_inputs<F: AlgebraicField>(_f: &F) -> Vec<ElementOf<F>> {
    Vec::new()
}

pub(crate) fn evaluate<F: AlgebraicField + SerializableField>(
    f: &F,
    circuit: &Circuit<F>,
    inputs: &[ElementOf<F>],
) -> Result<Evaluation<ElementOf<F>>, EvalError> {
    let raw = &circuit.raw;
    if inputs.len() != raw.ninput {
        return Err(EvalError::InputSizeMismatch {
            expected: raw.ninput,
            got: inputs.len(),
        });
    }
    let classes = classify_constants(f, &raw.constants);
    let mut values = inputs.to_vec();
    let mut failed_terms = Vec::new();
    for l in (0..raw.layers.len()).rev() {
        let noutput = if l == 0 {
            raw.noutput
        } else {
            raw.layers[l - 1].nw()
        };
        let (next, failed) = evaluate_layer(
            f,
            noutput,
            &raw.layers[l],
            &raw.constants,
            &classes,
            &values,
        );
        failed_terms.extend(failed.into_iter().map(|wire| (l, wire)));
        values = next;
    }
    Ok(Evaluation {
        failed_terms,
        outputs: values,
    })
}

fn evaluate_layer<F: AlgebraicField>(
    f: &F,
    noutput: usize,
    layer: &Layer,
    constants: &[ElementOf<F>],
    classes: &[CoefficientClass],
    vin: &[ElementOf<F>],
) -> (Vec<ElementOf<F>>, Vec<usize>) {
    let mut vout = vec![f.zero(); noutput];
    let mut failed_wires = Vec::new();
    layer.quadratic.for_each(|t| {
        let product = f.mulf(&vin[t.l as usize], &vin[t.r as usize]);
        if classes[t.k as usize] == CoefficientClass::Zero {
            if !f.is_zero(&product) {
                failed_wires.push(t.g as usize)
            }
        } else {
            f.add(
                &mut vout[t.g as usize],
                &f.mulf(&constants[t.k as usize], &product),
            )
        }
    });
    layer.linear.for_each(|t| {
        if classes[t.k as usize] == CoefficientClass::Zero {
            if !f.is_zero(&vin[t.l as usize]) {
                failed_wires.push(t.g as usize)
            }
        } else {
            f.add(
                &mut vout[t.g as usize],
                &f.mulf(&constants[t.k as usize], &vin[t.l as usize]),
            )
        }
    });
    layer
        .constant
        .for_each(|t| f.add(&mut vout[t.g as usize], &constants[t.k as usize]));
    failed_wires.sort_unstable();
    failed_wires.dedup();
    (vout, failed_wires)
}

/// Re-encode a circuit from one field into another through the circuit format.
pub(crate) fn convert<FC: SerializableField, FR: SerializableField>(
    fc: &FC,
    fr: &FR,
    circuit: &Circuit<FC>,
) -> Result<Circuit<FR>, String> {
    let bytes = CircuitWriter::new(fc).to_bytes(circuit);
    let (converted, remaining) = CircuitReader::new(fr).from_bytes(&bytes)?;
    if !remaining.is_empty() {
        return Err("Remaining bytes after deserialization".to_string());
    }
    Ok(converted)
}
