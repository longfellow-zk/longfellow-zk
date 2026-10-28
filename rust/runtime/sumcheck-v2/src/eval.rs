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

//! Circuit evaluation and assertion checks for the v2 prover.
//!
//! Circuit layers are stored from outputs toward inputs. Evaluate them in
//! reverse order, saving each layer's input witness before advancing to its
//! outputs. Return those witnesses in the original layer order for sumcheck.
//! Ordinary quads accumulate output values; assertion quads require their
//! input product to vanish. The final circuit outputs must all be zero.
use crate::{
    core::{
        algebra::SerializableField,
        proto::{circuit::Circuit, Layer},
    },
    runtime::algebra::RuntimeField,
};

/// Check all assertion products and final outputs, returning each layer's inputs
/// in sumcheck order (from the circuit outputs toward its inputs).
/// Start with the circuit input vector w; each layer produces the next vector.
pub(crate) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    circuit.validate_v2()?;
    let mut w_layers = Vec::with_capacity(circuit.raw.layers.len());
    for (layer_index, layer) in circuit.raw.layers.iter().enumerate().rev() {
        let noutput = if layer_index == 0 {
            circuit.raw.noutput
        } else {
            circuit.raw.layers[layer_index - 1].nw()
        };
        let outputs = eval_layer(&w, layer, &circuit.raw.constants, noutput, f).map_err(|e| {
            format!("Witness does not satisfy circuit constraints at layer {layer_index}: {e}")
        })?;
        w_layers.push(w);
        w = outputs;
    }
    // The last evaluated vector contains the circuit outputs, all required zero.
    for (g, value) in w.iter().enumerate() {
        if !f.is_zero(value) {
            return Err(format!("Circuit output at index {g} is not zero"));
        }
    }
    w_layers.reverse();
    Ok(w_layers)
}

/// Evaluate V[g] = sum_{l,r} QUAD[g,l,r]*W[l]*W[r] for ordinary quads.
/// Here w holds W and the returned vector holds V. A zero term coefficient is
/// an assertion marker: require W[l]*W[r] = 0 instead of accumulating an output.
pub(super) fn eval_layer<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &Layer<F>,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    if layer.coefficients().is_some() {
        return eval_partition(w, layer, constants, noutput, f);
    }
    let mut outputs = vec![f.zero(); noutput];
    let one = f.one();
    layer.try_for_each_term(constants, |term| {
        let g = term.g as usize;
        let l = term.h0 as usize;
        let r = term.h1 as usize;
        let product = f.mulf(&w[l], &w[r]);
        if f.is_zero(&term.k) {
            if !f.is_zero(&product) {
                return Err(format!(
                    "gate multiplication constraint not satisfied: wire_l={l}, wire_r={r}"
                ));
            }
        } else if term.k == one {
            f.add(&mut outputs[g], &product);
        } else {
            f.fma(&mut outputs[g], &term.k, &product);
        }
        Ok(())
    })?;
    if let Some([linear, constant]) = layer.affine() {
        let mone = f.mone();
        linear.for_each_term(constants, |t| {
            let output = &mut outputs[t.g as usize];
            let input = &w[t.h0 as usize];
            if t.k == one {
                f.add(output, input);
            } else if t.k == mone {
                f.sub(output, input);
            } else {
                f.fma(output, &t.k, input);
            }
        });
        constant.for_each_term(constants, |t| f.add(&mut outputs[t.g as usize], &t.k));
    }
    Ok(outputs)
}

fn eval_partition<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &Layer<F>,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut outputs = vec![f.zero(); noutput];
    let c = layer.coefficients().unwrap();
    layer.for_each_general_term(constants, |t| {
        f.fma(
            &mut outputs[t.g as usize],
            &t.k,
            &f.mulf(&w[t.h0 as usize], &w[t.h1 as usize]),
        )
    });
    c.units.for_each(|g, l, r| {
        f.add(
            &mut outputs[g as usize],
            &f.mulf(&w[l as usize], &w[r as usize]),
        )
    });
    c.assertions.try_for_each(|_, l, r| {
        if !f.is_zero(&f.mulf(&w[l as usize], &w[r as usize])) {
            return Err("quadratic assertion not satisfied".to_string());
        }
        Ok(())
    })?;
    if let Some([linear, constant]) = layer.affine() {
        let mone = f.mone();
        linear.for_each_general_term(constants, |t| {
            if t.k == mone {
                f.sub(&mut outputs[t.g as usize], &w[t.h0 as usize]);
            } else {
                f.fma(&mut outputs[t.g as usize], &t.k, &w[t.h0 as usize]);
            }
        });
        linear
            .coefficients()
            .unwrap()
            .units
            .for_each(|g, l, _| f.add(&mut outputs[g as usize], &w[l as usize]));
        constant.for_each_general_term(constants, |t| f.add(&mut outputs[t.g as usize], &t.k));
        linear
            .coefficients()
            .unwrap()
            .assertions
            .try_for_each(|_, l, _| {
                if f.is_zero(&w[l as usize]) {
                    Ok(())
                } else {
                    Err("linear assertion not satisfied".to_string())
                }
            })?;
        let one = f.one();
        constant
            .coefficients()
            .unwrap()
            .units
            .for_each(|g, _, _| f.add(&mut outputs[g as usize], &one));
    }
    Ok(outputs)
}
