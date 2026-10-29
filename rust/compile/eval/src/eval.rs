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
    compile::eval::{Circuit, Layer},
    core::algebra::ElementOf,
    runtime::algebra::field::RuntimeField,
};

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    UndefinedInput(usize),
    AssertionFailure,
    InputSizeMismatch { expected: usize, got: usize },
    ExcessiveInput,
}

pub fn initial_inputs<const W: usize, F: RuntimeField<W>>(_f: &F) -> Vec<ElementOf<F>> {
    Vec::new()
}

pub fn process_inputs<const W: usize, F: RuntimeField<W>>(
    _f: &F,
    ninput: usize,
    inputs: &[ElementOf<F>],
) -> Result<Vec<ElementOf<F>>, EvalError> {
    if inputs.len() == ninput {
        Ok(inputs.to_vec())
    } else {
        Err(EvalError::InputSizeMismatch {
            expected: ninput,
            got: inputs.len(),
        })
    }
}

pub fn eval_circuit<
    'a,
    const W: usize,
    FR: RuntimeField<W> + crate::core::algebra::SerializableField,
>(
    fr: &FR,
    circuit: &Circuit<FR>,
    symbols: &'a crate::compile::eval::CircuitDebugSymbols,
    inputs: &[ElementOf<FR>],
) -> crate::compile::eval::CompiledEvalAssertions<'a, EvalError> {
    let raw = &circuit.raw;
    let tracker = symbols.tracker();

    let vin = match process_inputs(fr, raw.ninput, inputs) {
        Ok(v) => v,
        Err(err) => {
            return crate::compile::eval::CompiledEvalAssertions {
                result: Err(err),
                fates: std::collections::HashMap::new(),
                tracker,
            };
        }
    };

    let mut current_v = vin;
    let mut fates = std::collections::HashMap::new();
    let mut overall_failed = false;

    for l in (0..raw.layers.len()).rev() {
        let noutput = if l == 0 {
            raw.noutput
        } else {
            raw.layers[l - 1].nw()
        };

        let (v, failed_wires) = eval_layer(fr, noutput, &raw.layers[l], &raw.constants, &current_v);
        current_v = v;
        if !failed_wires.is_empty() {
            overall_failed = true;
        }
        for index in failed_wires {
            let wire = crate::compile::eval::WireRef::new(l, index);
            if let Some(id) = symbols.get_id(&wire) {
                fates.insert(
                    id,
                    crate::compile::logic::scope::AssertionStatus::Failed(
                        "layer assertion failed".to_string(),
                    ),
                );
            }
        }
    }

    for (i, y) in current_v.iter().enumerate() {
        let wire = crate::compile::eval::WireRef::new(0, i);
        let is_ok = fr.is_zero(y);
        if !is_ok {
            overall_failed = true;
        }
        if let Some(id) = symbols.get_id(&wire) {
            let status = if is_ok {
                crate::compile::logic::scope::AssertionStatus::Passed
            } else {
                crate::compile::logic::scope::AssertionStatus::Failed(
                    "circuit output non-zero".to_string(),
                )
            };
            fates.entry(id).or_insert(status);
        }
    }

    crate::compile::eval::CompiledEvalAssertions {
        result: if overall_failed {
            Err(EvalError::AssertionFailure)
        } else {
            Ok(())
        },
        fates,
        tracker,
    }
}

fn eval_layer<FR: RuntimeField<W> + crate::core::algebra::SerializableField, const W: usize>(
    fr: &FR,
    noutput: usize,
    layer: &Layer,
    constants: &[ElementOf<FR>],
    vin: &[ElementOf<FR>],
) -> (Vec<ElementOf<FR>>, Vec<usize>) {
    let mut vout = vec![fr.zero(); noutput];
    let mut failed_wires = Vec::new();

    layer.quadratic.for_each(|t| {
        fr.fma(
            &mut vout[t.g as usize],
            &constants[t.k as usize],
            &fr.mulf(&vin[t.l as usize], &vin[t.r as usize]),
        )
    });
    layer.quadratic_one.for_each(|t| {
        fr.fma(
            &mut vout[t.g as usize],
            &vin[t.l as usize],
            &vin[t.r as usize],
        )
    });
    layer.quadratic_minus_one.for_each(|t| {
        fr.fnms(
            &mut vout[t.g as usize],
            &vin[t.l as usize],
            &vin[t.r as usize],
        )
    });
    layer.quadratic_assertions.for_each(|t| {
        if !fr.is_zero(&fr.mulf(&vin[t.l as usize], &vin[t.r as usize])) {
            failed_wires.push(t.g as usize);
        }
    });
    layer.linear.for_each(|t| {
        fr.fma(
            &mut vout[t.g as usize],
            &constants[t.k as usize],
            &vin[t.l as usize],
        )
    });
    layer
        .linear_one
        .for_each(|t| fr.add(&mut vout[t.g as usize], &vin[t.l as usize]));
    layer
        .linear_minus_one
        .for_each(|t| fr.sub(&mut vout[t.g as usize], &vin[t.l as usize]));
    layer.linear_assertions.for_each(|t| {
        if !fr.is_zero(&vin[t.l as usize]) {
            failed_wires.push(t.g as usize);
        }
    });
    layer
        .constant
        .for_each(|t| fr.add(&mut vout[t.g as usize], &constants[t.k as usize]));
    layer
        .constant_one
        .for_each(|t| fr.add(&mut vout[t.g as usize], &fr.one()));
    layer
        .constant_minus_one
        .for_each(|t| fr.sub(&mut vout[t.g as usize], &fr.one()));

    failed_wires.sort_unstable();
    failed_wires.dedup();
    (vout, failed_wires)
}

fn convert_circuit<
    FC: crate::core::algebra::SerializableField,
    FR: crate::core::algebra::SerializableField,
>(
    fc: &FC,
    fr: &FR,
    circuit: &Circuit<FC>,
    field_id: crate::core::proto::FieldID,
) -> Result<Circuit<FR>, String> {
    let writer = crate::core::proto::writer::CircuitWriter::new(fc, field_id);
    let bytes = writer.to_bytes_lfc3(circuit);
    let reader = crate::core::proto::reader::CircuitReader::new(fr, field_id);
    let (converted_circuit, remaining) = reader.from_bytes_lfc3(&bytes, true)?;
    if !remaining.is_empty() {
        return Err("Remaining bytes after deserialization".to_string());
    }

    Ok(converted_circuit)
}

pub fn eval_circuit_fc<
    'a,
    const WR: usize,
    FC: crate::core::algebra::SerializableField,
    FR: RuntimeField<WR> + crate::core::algebra::SerializableField,
>(
    fc: &FC,
    fr: &FR,
    circuit: &Circuit<FC>,
    symbols: &'a crate::compile::eval::CircuitDebugSymbols,
    inputs: &[ElementOf<FR>],
    field_id: crate::core::proto::FieldID,
) -> Result<crate::compile::eval::CompiledEvalAssertions<'a, EvalError>, String> {
    let converted = convert_circuit(fc, fr, circuit, field_id)?;
    Ok(eval_circuit(fr, &converted, symbols, inputs))
}
