// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

pub(crate) fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    w: Vec<F::E>,
    circuit: &Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    let layers = super::super::split::split_layers(circuit, f);
    eval_split_circuit(w, circuit, &layers, f)
}
