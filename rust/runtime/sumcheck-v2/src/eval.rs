// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic},
    },
    runtime::algebra::RuntimeField,
};
pub(crate) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    circuit.validate_v2()?;
    let mut saved = Vec::with_capacity(circuit.raw.layers.len());
    for (index, layer) in circuit.raw.layers.iter().enumerate().rev() {
        let noutput = if index == 0 {
            circuit.raw.noutput
        } else {
            circuit.raw.layers[index - 1].nw
        };
        let outputs = eval_layer(&w, layer, &circuit.raw.constants, noutput, f).map_err(|e| {
            format!("Witness does not satisfy circuit constraints at layer {index}: {e}")
        })?;
        saved.push(w);
        w = outputs;
    }
    for (g, x) in w.iter().enumerate() {
        if !f.is_zero(x) {
            return Err(format!("Circuit output at index {g} is not zero"));
        }
    }
    saved.reverse();
    Ok(saved)
}
pub(super) fn eval_layer<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &Layer,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut out = vec![f.zero(); noutput];
    layer.quadratic.try_for_each(|Quadratic { g, l, r, k }| {
        let product = f.mulf(&w[l as usize], &w[r as usize]);
        if k == 0 {
            if !f.is_zero(&product) {
                return Err("quadratic assertion not satisfied".to_string());
            }
        } else {
            f.fma(&mut out[g as usize], &constants[k as usize], &product);
        }
        Ok(())
    })?;
    layer.linear.try_for_each(|Linear { g, l, k }| {
        if k == 0 {
            if !f.is_zero(&w[l as usize]) {
                return Err("linear assertion not satisfied".to_string());
            }
        } else {
            f.fma(&mut out[g as usize], &constants[k as usize], &w[l as usize]);
        }
        Ok(())
    })?;
    layer
        .constant
        .for_each(|Constant { g, k }| f.add(&mut out[g as usize], &constants[k as usize]));
    Ok(out)
}
