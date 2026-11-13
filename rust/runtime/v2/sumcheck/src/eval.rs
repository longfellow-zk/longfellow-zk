// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    circuit::CircuitSource,
    split::{ConstantCoordinates, LinearCoordinates, QuadraticCoordinates, SplitLayer},
};
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{Constant, Linear, Quadratic},
    },
    runtime::algebra::RuntimeField,
};

/// Add one fragment's terms to its slice of the common layer output array.
pub(super) fn eval_layer_into<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    out: &mut [F::E],
    f: &F,
) -> Result<(), String> {
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
    Ok(())
}

#[cfg(test)]
#[path = "../tests/eval_fixtures.rs"]
mod fixtures;
#[cfg(test)]
pub(crate) use fixtures::eval_circuit;
#[cfg(test)]
pub(super) use fixtures::{eval_layer, eval_split_circuit};

/// Evaluate the quad fragments from common inputs toward circuit outputs.
/// Each saved witness is one complete global layer. Completed circuits' zero
/// outputs are checked before dropping their slots; the remaining slots already
/// have the next layer's ordering.
pub(super) fn eval_circuits<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuits: &[impl CircuitSource<F>],
    layers: &[Vec<SplitLayer<'_>>],
    schedule: &super::fragments::Schedule,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    if w.len() != schedule.ninput {
        return Err("shared input width mismatch".into());
    }
    // A zero-layer component's outputs are its own input prefix.
    for c in circuits.iter().filter(|c| c.raw().layers.is_empty()) {
        if let Some(g) = w[..c.raw().ninput].iter().position(|v| !f.is_zero(v)) {
            return Err(format!("Circuit output at index {g} is not zero"));
        }
    }
    let mut saved = Vec::with_capacity(schedule.layers.len());
    for (stage, layout) in schedule.layers.iter().enumerate().rev() {
        assert_eq!(w.len(), layout.nw);
        let mut out = vec![f.zero(); layout.nv];
        for s in &layout.fragments {
            eval_layer_into(&w[s.input_range.clone()], &layers[s.circuit][s.layer],
                &circuits[s.circuit].raw().constants, &mut out[s.output_range.clone()], f)
                .map_err(|e| format!("Witness does not satisfy circuit constraints at stage {stage}, circuit {}: {e}", s.circuit))?;
        }
        // Depth ordering places the completed circuits' outputs at the tail.
        // Check every one, then retain the preceding global array in place.
        let carried = layout.nv - layout.output_assertions;
        if let Some(g) = out[carried..].iter().position(|v| !f.is_zero(v)) {
            return Err(format!(
                "Circuit output at index {} is not zero",
                carried + g
            ));
        }
        out.truncate(carried);
        saved.push(w);
        w = out;
    }
    saved.reverse();
    Ok(saved)
}
