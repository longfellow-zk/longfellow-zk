// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core::proto::v2::Circuit;

pub(crate) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    let layers = super::super::split::split_layers(circuit, f);
    eval_split_circuit(w, circuit, &layers, f)
}

pub(crate) fn eval_split_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &crate::core::proto::v2::Circuit<F>,
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
pub(crate) fn eval_layer<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: &[F::E],
    layer: &SplitLayer<'_>,
    constants: &[F::E],
    noutput: usize,
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut out = vec![f.zero(); noutput];
    eval_layer_into(w, layer, constants, &mut out, f)?;
    Ok(out)
}
