// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use core_algebra::SerializableField;
use core_proto::{circuit::Circuit, Layer};
use runtime_algebra::RuntimeField;

/// Layer inputs and assertion outputs collected in the same circuit traversal.
#[derive(Debug)]
pub struct EvaluatedLayer<E> {
    pub inputs: Vec<E>,
    pub assertion_outputs: Vec<bool>,
}

/// Evaluate from inputs to outputs, returning layers in sumcheck order.
pub fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut inputs: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<EvaluatedLayer<F::E>>, String> {
    let mut layers = Vec::with_capacity(circuit.raw.layers.len());
    for (index, layer) in circuit.raw.layers.iter().enumerate().rev() {
        let output_width = if index == 0 {
            circuit.raw.noutput
        } else {
            circuit.raw.layers[index - 1].nw()
        };
        let mut assertion_outputs = vec![false; output_width];
        let outputs = eval_quad(
            &inputs,
            layer,
            &circuit.raw.constants,
            &mut assertion_outputs,
            f,
        )
        .map_err(|e| {
            format!("Witness does not satisfy circuit constraints at layer {index}: {e}")
        })?;
        layers.push(EvaluatedLayer {
            inputs,
            assertion_outputs,
        });
        inputs = outputs;
    }
    for (index, value) in inputs.iter().enumerate() {
        if !f.is_zero(value) {
            return Err(format!(
                "Circuit output at index {index} is not zero: {value:?}"
            ));
        }
    }
    layers.reverse();
    Ok(layers)
}

fn eval_quad<const W: usize, F: RuntimeField<W> + SerializableField>(
    inputs: &[F::E],
    layer: &Layer<F>,
    constants: &[F::E],
    assertions: &mut [bool],
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut outputs = vec![f.zero(); assertions.len()];
    let one = f.one();
    layer.try_for_each_term(constants, |term| {
        let g = term.g as usize;
        let r = term.h0 as usize;
        let l = term.h1 as usize;
        let mut product = f.mulf(&inputs[l], &inputs[r]);
        if f.is_zero(&term.k) {
            mark_assertion(assertions, g)?;
            if !f.is_zero(&product) {
                return Err(format!(
                    "gate multiplication constraint not satisfied: left_wire={l}, right_wire={r}, left_val={:?}, right_val={:?}, computed_val={product:?}",
                    inputs[l], inputs[r],
                ));
            }
        } else {
            if term.k != one { f.mul(&mut product, &term.k); }
            f.add(&mut outputs[g], &product);
        }
        Ok(())
    })?;
    Ok(outputs)
}

/// Discover assertion outputs without a witness, for independent verification.
pub fn assertion_outputs<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    output_width: usize,
    f: &F,
) -> Result<Vec<bool>, String> {
    let mut outputs = vec![false; output_width];
    layer.try_for_each_term(constants, |term| {
        if term.g as usize >= output_width {
            return Err("term output exceeds layer width".to_string());
        }
        if f.is_zero(&term.k) {
            mark_assertion(&mut outputs, term.g as usize)?;
        }
        Ok(())
    })?;
    Ok(outputs)
}

// Each assertion output must have one marker: multiple products could cancel.
fn mark_assertion(outputs: &mut [bool], index: usize) -> Result<(), String> {
    let output = outputs
        .get_mut(index)
        .ok_or("term output exceeds layer width")?;
    if *output {
        return Err("multiple assertion markers at one output".into());
    }
    *output = true;
    Ok(())
}
