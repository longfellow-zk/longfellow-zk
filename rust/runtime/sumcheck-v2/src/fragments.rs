// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Sparse quad fragments describe one circuit with a shared input array and
//! one wire array per intermediate layer. Intermediate wires are concatenated
//! in circuit order, without padding. The fragments retain local gate indices;
//! their ranges translate those indices into the global arrays. At the input
//! boundary every fragment addresses the same array with input offset zero.
//!
//! Shorter circuits enter later when their remaining depth matches the others.
//! Their outputs must vanish; fresh weights on those outputs add zero to the
//! running claim. The ordinary sumcheck kernel sees only the resulting global
//! wire arrays. Fragmentation matters only when traversing the sparse terms.
use std::ops::Range;

use super::{
    quad::{affine_constant, affine_linear, bind_l_into},
    split::SplitLayer,
    transcript::assertion_weights,
    SumcheckProofGeometry,
};
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        random::{RandomEngine, Transcript},
    },
};

/// Locate one circuit layer's sparse terms in the global layer arrays.
/// Quadratic, linear and constant streams use the same offsets. These ranges
/// describe gate addressing; the fragment owns no wire values or dense weights.
#[derive(Clone)]
pub(super) struct QuadFragment {
    pub circuit: usize,
    pub layer: usize,
    pub input_range: Range<usize>,
    pub output_range: Range<usize>,
}
pub(super) struct LayerLayout {
    pub fragments: Vec<QuadFragment>,
    pub nw: usize,
    pub nv: usize,
}
pub(super) struct Schedule {
    pub geometry: SumcheckProofGeometry,
    pub layers: Vec<LayerLayout>,
    pub ninput: usize,
}
impl Schedule {
    pub fn new<F: SerializableField>(circuits: &[&Circuit<F>]) -> Result<Self, String> {
        let first = circuits.first().ok_or("empty circuit list")?;
        let ninput = first.raw.ninput;
        let npublic = first.raw.npublic_input;
        if npublic > ninput
            || circuits.iter().any(|c| {
                c.raw.ninput != ninput
                    || c.raw.npublic_input != npublic
                    || c.raw
                        .layers
                        .last()
                        .map_or(c.raw.noutput != ninput, |l| l.nw != ninput)
            })
        {
            return Err("circuits must share one input layout".into());
        }
        let depth = circuits.iter().map(|c| c.raw.layers.len()).max().unwrap();
        let mut layers = Vec::with_capacity(depth);
        for stage in 0..depth {
            let shared_inputs = stage + 1 == depth;
            let mut nw = 0usize;
            let mut nv = 0usize;
            let mut fragments = Vec::new();
            for (circuit, c) in circuits.iter().enumerate() {
                if let Some(layer) = stage.checked_sub(depth - c.raw.layers.len()) {
                    let width = c.raw.layers[layer].nw;
                    if width == 0 {
                        return Err("sumcheck layer must contain a wire".into());
                    }
                    let outputs = if layer == 0 {
                        c.raw.noutput
                    } else {
                        c.raw.layers[layer - 1].nw
                    };
                    let next_v = nv
                        .checked_add(outputs)
                        .ok_or("virtual output width overflow")?;
                    let inputs = if shared_inputs {
                        0..ninput
                    } else {
                        let end = nw
                            .checked_add(width)
                            .ok_or("virtual input width overflow")?;
                        let range = nw..end;
                        nw = end;
                        range
                    };
                    fragments.push(QuadFragment {
                        circuit,
                        layer,
                        input_range: inputs,
                        output_range: nv..next_v,
                    });
                    nv = next_v;
                }
            }
            if shared_inputs {
                nw = ninput;
            }
            layers.push(LayerLayout { fragments, nw, nv });
        }
        let geometry = SumcheckProofGeometry::new(
            layers
                .iter()
                .map(|s| crate::util::ceil_log2(s.nw))
                .collect(),
        );
        geometry.serialized_elements().map_err(|e| e.to_string())?;
        Ok(Self {
            geometry,
            layers,
            ninput,
        })
    }
    pub fn bind<F: SerializableField>(&self, circuits: &[&Circuit<F>], t: &mut Transcript) {
        t.write_bytes(b"layered-sumcheck/circuits/v1");
        t.write_bytes(&(circuits.len() as u64).to_le_bytes());
        for c in circuits {
            t.write_bytes(&c.id);
            t.write_bytes(&(c.raw.layers.len() as u64).to_le_bytes());
        }
    }
    /// Carry the previous global weights forward and insert weights only for
    /// newly entering zero outputs. Without new circuits the array is reused.
    pub fn enter<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
        &self,
        circuits: &[&Circuit<F>],
        weights: &mut Vec<F::E>,
        stage: usize,
        t: &mut Transcript,
        f: &F,
    ) {
        let sample = |i: usize, t: &mut Transcript| {
            t.write_bytes(b"layered-sumcheck/enter-circuit/v1");
            t.write_bytes(&(i as u64).to_le_bytes());
            t.elt_field_slice(circuits[i].raw.noutput, f)
        };
        if stage == self.layers.len() {
            // Zero-layer circuits assert that the common inputs themselves
            // vanish. Their output weights join the same final input claim.
            if self.layers.is_empty() {
                weights.resize(self.ninput, f.zero());
            }
            assert_eq!(weights.len(), self.ninput);
            for (i, c) in circuits.iter().enumerate() {
                if c.raw.layers.is_empty() {
                    blas::add(weights, &sample(i, t), f);
                }
            }
            return;
        }
        let layout = &self.layers[stage];
        if layout.fragments.iter().any(|s| s.layer == 0) {
            let mut old = std::mem::take(weights).into_iter();
            let mut next = Vec::with_capacity(layout.nv);
            for s in &layout.fragments {
                if s.layer == 0 {
                    next.extend(sample(s.circuit, t));
                } else {
                    next.extend(old.by_ref().take(s.output_range.len()));
                }
            }
            assert!(old.next().is_none());
            *weights = next;
        }
        assert_eq!(weights.len(), layout.nv);
    }
}

pub(crate) fn geometry<F: SerializableField>(
    circuits: &[&Circuit<F>],
) -> Result<SumcheckProofGeometry, String> {
    Ok(Schedule::new(circuits)?.geometry)
}

/// The eleven-way split and assertion coefficients for one quad fragment.
/// Wire values and output weights are borrowed from the global layer arrays.
pub(super) struct SplitFragment<'a, E> {
    pub fragment: QuadFragment,
    pub layer: SplitLayer<'a>,
    pub assertions: Vec<E>,
}
impl<'a, E> SplitFragment<'a, E> {
    pub fn new<const W: usize, F: RuntimeField<W, E = E> + SerializableField + SupportsSampling>(
        fragment: &QuadFragment,
        layer: SplitLayer<'a>,
        t: &mut Transcript,
        f: &F,
    ) -> Self {
        assert_eq!(layer.nw, fragment.input_range.len());
        t.write_bytes(b"layered-sumcheck/assertions/v1");
        t.write_bytes(&(fragment.circuit as u64).to_le_bytes());
        let assertions = assertion_weights(&layer, fragment.layer, t, f);
        Self {
            fragment: fragment.clone(),
            layer,
            assertions,
        }
    }
}
pub(super) fn constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    circuits: &[&Circuit<F>],
    weights: &[F::E],
    active: &[SplitFragment<'_, F::E>],
    f: &F,
) -> F::E {
    let mut constant = f.zero();
    for a in active {
        let s = &a.fragment;
        f.add(
            &mut constant,
            &affine_constant(
                &a.layer,
                &circuits[s.circuit].raw.constants,
                &weights[s.output_range.clone()],
                f,
            ),
        );
    }
    constant
}

/// Bind every fragment's sparse terms against slices of one monomial array.
/// Accumulate Q into one global array; input-layer fragments deliberately overlap.
/// Finally apply the ordinary a_next=m(u)+alpha*q_r update once over that array.
pub(super) fn transition<const W: usize, F: RuntimeField<W> + SerializableField>(
    circuits: &[&Circuit<F>],
    weights: &[F::E],
    active: &[SplitFragment<'_, F::E>],
    nw: usize,
    point: &[F::E],
    alpha: &F::E,
    f: &F,
) -> (Vec<F::E>, F::E) {
    let mut m = super::monomial::weights(crate::util::ceil_log2(nw), nw, point, f);
    let mut q = vec![f.zero(); nw];
    let mut linear = f.zero();
    for a in active {
        let s = &a.fragment;
        let constants = &circuits[s.circuit].raw.constants;
        let output_weights = &weights[s.output_range.clone()];
        let input_weights = &m[s.input_range.clone()];
        bind_l_into(
            &a.layer,
            constants,
            output_weights,
            &a.assertions,
            input_weights,
            &mut q[s.input_range.clone()],
            f,
        );
        f.add(
            &mut linear,
            &affine_linear(
                &a.layer,
                constants,
                output_weights,
                &a.assertions,
                input_weights,
                f,
            ),
        );
    }
    blas::axpy(&mut m, alpha, &q, f);
    (m, linear)
}

#[cfg(test)]
#[path = "../tests/fragments.rs"]
mod tests;
