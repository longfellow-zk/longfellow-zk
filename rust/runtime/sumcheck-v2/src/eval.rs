// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::split::{ConstantCoordinates, LinearCoordinates, QuadraticCoordinates, SplitLayer};
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{Circuit, Constant, Linear, Quadratic},
    },
    runtime::algebra::RuntimeField,
};

#[cfg(test)]
pub(crate) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    circuit.validate_v2()?;
    let layers: Vec<_> = circuit.raw.layers.iter().map(SplitLayer::new).collect();
    eval_split_circuit(w, circuit, &layers, f)
}

pub(super) fn eval_split_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &Circuit<F>,
    layers: &[SplitLayer<'_>],
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    let mut saved = Vec::with_capacity(layers.len());
    for (index, layer) in layers.iter().enumerate().rev() {
        let noutput = if index == 0 {
            circuit.raw.noutput
        } else {
            layers[index - 1].nw
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
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut out = vec![f.zero(); noutput];
    layer
        .quadratic
        .for_each(&layer.quadratic_runs, |Quadratic { g, l, r, k }| {
            f.fma(
                &mut out[g as usize],
                &constants[k as usize],
                &f.mulf(&w[l as usize], &w[r as usize]),
            );
        });
    layer
        .quadratic_one
        .for_each(&layer.quadratic_runs, |QuadraticCoordinates { g, l, r }| {
            f.fma(&mut out[g as usize], &w[l as usize], &w[r as usize]);
        });
    layer.quadratic_minus_one.for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g, l, r }| {
            f.fnms(&mut out[g as usize], &w[l as usize], &w[r as usize]);
        },
    );
    layer.quadratic_assertions.try_for_each(
        &layer.quadratic_runs,
        |QuadraticCoordinates { g: _, l, r }| {
            if !f.is_zero(&f.mulf(&w[l as usize], &w[r as usize])) {
                return Err("quadratic assertion not satisfied".to_string());
            }
            Ok(())
        },
    )?;
    layer
        .linear
        .for_each(&layer.linear_runs, |Linear { g, l, k }| {
            f.fma(&mut out[g as usize], &constants[k as usize], &w[l as usize]);
        });
    layer
        .linear_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.add(&mut out[g as usize], &w[l as usize]);
        });
    layer
        .linear_minus_one
        .for_each(&layer.linear_runs, |LinearCoordinates { g, l }| {
            f.sub(&mut out[g as usize], &w[l as usize]);
        });
    layer
        .linear_assertions
        .try_for_each(&layer.linear_runs, |LinearCoordinates { g: _, l }| {
            if !f.is_zero(&w[l as usize]) {
                return Err("linear assertion not satisfied".to_string());
            }
            Ok(())
        })?;
    layer
        .constant
        .for_each(&layer.constant_runs, |Constant { g, k }| {
            f.add(&mut out[g as usize], &constants[k as usize])
        });
    let one = f.one();
    layer
        .constant_one
        .for_each(&layer.constant_runs, |ConstantCoordinates { g }| {
            f.add(&mut out[g as usize], &one);
        });
    layer
        .constant_minus_one
        .for_each(&layer.constant_runs, |ConstantCoordinates { g }| {
            f.sub(&mut out[g as usize], &one);
        });
    Ok(out)
}
