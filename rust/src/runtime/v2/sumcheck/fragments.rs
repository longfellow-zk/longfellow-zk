// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Sparse quad fragments describe one circuit with a shared input array and
//! one wire array per intermediate layer. Components are ordered by decreasing
//! depth, preserving their supplied order at equal depths. Intermediate wires
//! are concatenated in that order, without padding. Fragments retain local gate indices;
//! their ranges translate those indices into the global arrays. At the input
//! boundary every fragment addresses the same array with input offset zero,
//! reading the prefix given by its own `ninput`. The shared array is as wide as
//! the widest component; narrower components cannot address its suffix.
//!
//! Shorter circuits enter later when their remaining depth matches the others.
//! Their outputs must vanish; fresh assertion weights on those outputs add zero to the
//! running claim. The ordinary sumcheck kernel sees only the resulting global
//! wire arrays. Fragmentation matters only when traversing the sparse terms.
use std::ops::Range;

use super::{
    circuit::CircuitSource,
    quad::{affine_constant, affine_linear, bind_l_into},
    split::SplitLayer,
};
#[cfg(test)]
use crate::core::proto::v2::Circuit;
use crate::{
    core::{
        algebra::SerializableField,
        proto::{
            v2::{classify_constants, CoefficientClass},
            DigestBytes,
        },
    },
    runtime::{
        algebra::{blas, RuntimeField},
        v2::proto::sumcheck::SumcheckProofGeometry,
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
    pub output_assertions: usize,
}
/// The shared layout of a circuit list and what the run time derives from
/// each circuit's coefficients: its classes (`classify_constants`) and, for
/// each layer, its quadratic and linear assertion counts. A role builds it
/// once, when it draws the top weights (`top_weights`), and carries it in
/// them to the sumcheck; nothing rebuilds or recounts it. `ids` names the
/// circuits it was built for, in list order.
pub(super) struct Schedule {
    pub geometry: SumcheckProofGeometry,
    pub layers: Vec<LayerLayout>,
    pub ninput: usize,
    ids: Vec<DigestBytes>,
    classes: Vec<Vec<CoefficientClass>>,
    assertions: Vec<Vec<[usize; 2]>>,
}
impl Schedule {
    pub(super) fn new<F: SerializableField>(
        circuits: &[impl CircuitSource<F>],
        f: &F,
    ) -> Result<Self, String> {
        let (geometry, layers, ninput) = Self::layout(circuits)?;
        let classes: Vec<_> = circuits
            .iter()
            .map(|c| classify_constants(f, &c.raw().constants))
            .collect();
        let assertions = circuits
            .iter()
            .zip(&classes)
            .map(|(c, k)| {
                c.raw()
                    .layers
                    .iter()
                    .map(|l| l.assertion_counts(k))
                    .collect()
            })
            .collect();
        Ok(Self {
            geometry,
            layers,
            ninput,
            ids: circuits.iter().map(|c| *c.id()).collect(),
            classes,
            assertions,
        })
    }
    /// Whether this schedule was built for `circuits`, in this order.
    pub(super) fn is_for<F: SerializableField>(&self, circuits: &[impl CircuitSource<F>]) -> bool {
        self.ids.len() == circuits.len()
            && self.ids.iter().zip(circuits).all(|(id, c)| id == c.id())
    }
    /// A fragment's quadratic and linear assertion counts.
    pub(super) fn assertion_counts(&self, fragment: &QuadFragment) -> [usize; 2] {
        self.assertions[fragment.circuit][fragment.layer]
    }
    /// Split one fragment's layer with the schedule's classes and counts.
    #[cfg(any(test, feature = "verifier"))]
    pub(super) fn split<'a, F: SerializableField + 'a>(
        &self,
        circuits: &'a [impl CircuitSource<F>],
        fragment: &QuadFragment,
    ) -> SplitLayer<'a> {
        let (c, j) = (fragment.circuit, fragment.layer);
        SplitLayer::with_classes(
            &circuits[c].raw().layers[j],
            &self.classes[c],
            self.assertions[c][j],
        )
    }
    /// Split every layer of every circuit, in list order.
    #[cfg(any(test, feature = "prover"))]
    pub(super) fn split_layers<'a, F: SerializableField + 'a>(
        &self,
        circuits: &'a [impl CircuitSource<F>],
    ) -> Vec<Vec<SplitLayer<'a>>> {
        circuits
            .iter()
            .enumerate()
            .map(|(c, circuit)| {
                circuit
                    .raw()
                    .layers
                    .iter()
                    .zip(&self.assertions[c])
                    .map(|(l, &n)| SplitLayer::with_classes(l, &self.classes[c], n))
                    .collect()
            })
            .collect()
    }

    /// The proof geometry, the stage layouts and the shared input width,
    /// which depend only on the circuits' widths and depths.
    #[allow(clippy::type_complexity)]
    fn layout<F: SerializableField>(
        circuits: &[impl CircuitSource<F>],
    ) -> Result<(SumcheckProofGeometry, Vec<LayerLayout>, usize), String> {
        let first = circuits.first().ok_or("empty circuit list")?;
        // Components share one input array whose width is the largest declared
        // width. Each component reads only its own prefix, so a component can
        // never address inputs beyond its own `ninput`. The public prefix is
        // common to every component.
        let ninput = circuits.iter().map(|c| c.raw().ninput).max().unwrap();
        let npublic = first.raw().npublic_input;
        if circuits.iter().any(|c| {
            let width = c.raw().ninput;
            c.raw().npublic_input != npublic
                || npublic > width
                || c.raw()
                    .layers
                    .last()
                    .map_or(c.raw().noutput != width, |l| l.nw != width)
        }) {
            return Err("circuits must share one input layout".into());
        }
        let depth = circuits.iter().map(|c| c.raw().layers.len()).max().unwrap();
        // Once ordered by depth, entering circuits always append to the active
        // layout. The protocol can extend its carried weights in place, with
        // no first-layer branch, placeholder coefficients or weight shuffling.
        let mut order: Vec<_> = (0..circuits.len()).collect();
        // The supplied list is transcript-bound. Its index is the explicit
        // tie-breaker, including for repeated circuit IDs.
        order.sort_by_key(|&i| (std::cmp::Reverse(circuits[i].raw().layers.len()), i));
        let mut layers = Vec::with_capacity(depth);
        for stage in 0..depth {
            let shared_inputs = stage + 1 == depth;
            let mut nw = 0usize;
            let mut nv = 0usize;
            let mut output_assertions = 0usize;
            let mut fragments = Vec::new();
            for &circuit in &order {
                let c = &circuits[circuit];
                if let Some(layer) = stage.checked_sub(depth - c.raw().layers.len()) {
                    let width = c.raw().layers[layer].nw;
                    if width == 0 {
                        return Err("sumcheck layer must contain a wire".into());
                    }
                    let outputs = if layer == 0 {
                        c.raw().noutput
                    } else {
                        c.raw().layers[layer - 1].nw
                    };
                    let next_v = nv
                        .checked_add(outputs)
                        .ok_or("virtual output width overflow")?;
                    if layer == 0 {
                        output_assertions = output_assertions
                            .checked_add(outputs)
                            .ok_or("output assertion count overflow")?;
                    }
                    let inputs = if shared_inputs {
                        0..c.raw().ninput
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
            layers.push(LayerLayout {
                fragments,
                nw,
                nv,
                output_assertions,
            });
        }
        let geometry = SumcheckProofGeometry::new(
            layers
                .iter()
                .map(|s| crate::util::ceil_log2(s.nw))
                .collect(),
        )
        .map_err(|e| e.to_string())?;
        Ok((geometry, layers, ninput))
    }
}

pub(crate) fn circuit_geometry<F: SerializableField>(
    circuits: &[impl CircuitSource<F>],
) -> Result<SumcheckProofGeometry, String> {
    Ok(Schedule::layout(circuits)?.0)
}

/// The eleven-way split and assertion coefficients for one quad fragment.
/// Wire values and output weights are borrowed from the global layer arrays.
pub(super) struct SplitFragment<'a, E> {
    pub fragment: QuadFragment,
    pub layer: SplitLayer<'a>,
    pub assertions: Vec<E>,
}
impl<'a, E> SplitFragment<'a, E> {
    pub(super) fn new(fragment: &QuadFragment, layer: SplitLayer<'a>) -> Self {
        assert_eq!(layer.nw, fragment.input_range.len());
        Self {
            fragment: fragment.clone(),
            layer,
            assertions: Vec::new(),
        }
    }
}

pub(super) fn constant<const W: usize, F: RuntimeField<W> + SerializableField>(
    circuits: &[impl CircuitSource<F>],
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
                &circuits[s.circuit].raw().constants,
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
    circuits: &[impl CircuitSource<F>],
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
        let constants = &circuits[s.circuit].raw().constants;
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
mod tests;
