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

//! Evaluate the v1 circuit witness from inputs toward outputs.
//!
//! Each layer computes V[g]=sum_{l,r} QUAD[g,l,r]*W[l]*W[r]. Zero coefficients
//! mark assertions W[l]*W[r]=0 instead of contributions to V. Keep each input
//! witness in output-to-input circuit order for the subsequent sumcheck proof,
//! and require every final circuit output to vanish.
use crate::{core::algebra::SerializableField, runtime::algebra::field::RuntimeField};

/// Return each layer's input witness after checking assertions and final outputs.
pub fn eval_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    mut w: Vec<F::E>,
    circuit: &crate::core::proto::v1::Circuit<F>,
    f: &F,
) -> Result<Vec<Vec<F::E>>, String> {
    let nl = circuit.raw.layers.len();
    let mut in_layers = vec![Vec::new(); nl];

    for l in (0..nl).rev() {
        let nv = if l > 0 {
            circuit.raw.layers[l - 1].nw()
        } else {
            circuit.raw.noutput
        };

        let v =
            eval_quad(nv, &w, &circuit.raw.layers[l], &circuit.raw.constants, f).map_err(|e| {
                format!("Witness does not satisfy circuit constraints at layer {l}: {e}")
            })?;

        in_layers[l] = w;
        w = v;
    }

    for (i, val) in w.iter().enumerate() {
        if !f.is_zero(val) {
            return Err(format!("Circuit output at index {i} is not zero: {val:?}"));
        }
    }

    Ok(in_layers)
}

/// Evaluate one layer, traversing sparse terms in the circuit's stored order.
pub fn eval_quad<const W: usize, F: RuntimeField<W> + SerializableField>(
    nv: usize,
    w: &[F::E],
    layer: &crate::core::proto::v1::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Result<Vec<F::E>, String> {
    let mut v = vec![f.zero(); nv];

    layer.try_for_each_term(constants, #[inline(always)] |term| {
        let g = term.g as usize;
        let r = term.h0 as usize;
        let l = term.h1 as usize;

        let wl = &w[l];
        let wr = &w[r];

        if f.is_zero(&term.k) {
            let mut y = wl.clone();
            f.mul(&mut y, wr);
            if !f.is_zero(&y) {
                return Err(format!(
                    "gate multiplication constraint not satisfied: left_wire={l}, right_wire={r}, left_val={wl:?}, right_val={wr:?}, computed_val={y:?}"
                ));
            }
        } else {
            let mut x = term.k;
            f.mul(&mut x, wl);
            f.mul(&mut x, wr);
            f.add(&mut v[g], &x);
        }
        Ok(())
    })?;
    Ok(v)
}
