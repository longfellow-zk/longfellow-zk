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

use std::fmt;

use crate::core::algebra::SerializableField;

pub struct Term<F: SerializableField> {
    pub k: F::E,
    pub g: u32,
    pub h0: u32,
    pub h1: u32,
}

impl<F: SerializableField> Clone for Term<F> {
    fn clone(&self) -> Self {
        Term {
            k: self.k.clone(),
            g: self.g,
            h0: self.h0,
            h1: self.h1,
        }
    }
}

impl<F: SerializableField> PartialEq for Term<F>
where F::E: PartialEq
{
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g && self.h0 == other.h0 && self.h1 == other.h1 && self.k == other.k
    }
}

impl<F: SerializableField> Eq for Term<F> where F::E: Eq {}

impl<F: SerializableField> fmt::Debug for Term<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Term")
            .field("k", &self.k)
            .field("g", &self.g)
            .field("h0", &self.h0)
            .field("h1", &self.h1)
            .finish()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, Debug)]
pub struct TermDelta {
    pub g: u32,
    pub h: [u32; 2],
    pub k_index: u32,
}

pub struct Layer<F: SerializableField> {
    pub(in crate::core::proto) coefficients: Option<Box<super::fixed::FixedCoefficients<F>>>,
    /// degree-only experiment stores linear and constant streams separately. These child streams
    /// have no affine children; their unused input indices are zero.
    pub(in crate::core::proto) affine: Option<Box<[Layer<F>; 2]>>,
    pub(in crate::core::proto) nw: usize,
    pub(in crate::core::proto) logw: usize,
    pub(in crate::core::proto) deltas: Vec<TermDelta>,
    pub(in crate::core::proto) delta_segments: Vec<Vec<u32>>,
    pub(in crate::core::proto) delta_tokens: Vec<u32>,
    pub(in crate::core::proto) _marker: std::marker::PhantomData<F>,
}

impl<F: SerializableField> Layer<F> {
    pub fn new(
        nw: usize,
        logw: usize,
        deltas: Vec<TermDelta>,
        delta_segments: Vec<Vec<u32>>,
        delta_tokens: Vec<u32>,
    ) -> Self {
        Self {
            affine: None,
            coefficients: None,
            nw,
            logw,
            deltas,
            delta_segments,
            delta_tokens,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn with_affine(mut self, linear: Layer<F>, constant: Layer<F>) -> Self {
        assert!(linear.affine.is_none() && constant.affine.is_none());
        self.affine = Some(Box::new([linear, constant]));
        self
    }

    pub fn with_coefficients(mut self, coefficients: super::fixed::FixedCoefficients<F>) -> Self {
        self.coefficients = Some(Box::new(coefficients));
        self
    }
    pub fn coefficients(&self) -> Option<&super::fixed::FixedCoefficients<F>> {
        self.coefficients.as_deref()
    }

    pub fn has_linear_assertions(&self) -> bool {
        self.affine().is_some_and(|a| {
            a[0].coefficients()
                .is_some_and(|c| matches!(&c.assertions, super::fixed::UnitTerms::Linear(_)))
        })
    }
    pub fn linear_assertion_count(&self) -> usize {
        self.affine()
            .and_then(|a| a[0].coefficients())
            .map_or(0, |c| c.assertions.num_terms())
    }

    pub fn affine(&self) -> Option<&[Layer<F>; 2]> {
        self.affine.as_deref()
    }

    pub fn streams(&self) -> impl Iterator<Item = &Layer<F>> {
        std::iter::once(self).chain(self.affine.iter().flat_map(|a| a.iter()))
    }

    /// Owned allocation capacity, excluding this Layer value and allocator metadata.
    pub fn heap_bytes(&self) -> usize {
        self.coefficients.as_ref().map_or(0, |c| {
            std::mem::size_of::<super::fixed::FixedCoefficients<F>>() + c.heap_bytes()
        }) + self.deltas.capacity() * std::mem::size_of::<TermDelta>()
            + self.delta_segments.capacity() * std::mem::size_of::<Vec<u32>>()
            + self
                .delta_segments
                .iter()
                .map(|s| s.capacity() * 4)
                .sum::<usize>()
            + self.delta_tokens.capacity() * 4
            + self.affine.as_ref().map_or(0, |a| {
                std::mem::size_of::<[Layer<F>; 2]>() + a.iter().map(Self::heap_bytes).sum::<usize>()
            })
    }

    pub fn remap_constants(&mut self, mapping: &[u32]) {
        for d in &mut self.deltas {
            d.k_index = mapping[d.k_index as usize];
        }
        if let Some(streams) = &mut self.affine {
            for stream in streams.iter_mut() {
                stream.remap_constants(mapping);
            }
        }
    }

    #[inline(always)]
    #[must_use]
    pub fn deltas(&self) -> &[TermDelta] {
        &self.deltas
    }

    #[inline(always)]
    pub fn deltas_mut(&mut self) -> &mut [TermDelta] {
        &mut self.deltas
    }

    #[inline(always)]
    #[must_use]
    pub fn delta_segments(&self) -> &[Vec<u32>] {
        &self.delta_segments
    }

    #[inline(always)]
    #[must_use]
    pub fn delta_tokens(&self) -> &[u32] {
        &self.delta_tokens
    }

    pub(in crate::core::proto) fn new_uncompressed(
        nw: usize,
        logw: usize,
        deltas: Vec<TermDelta>,
        delta_sequence: Vec<u32>,
    ) -> Self {
        Self::new(nw, logw, deltas, vec![delta_sequence], vec![0])
    }

    /// Constructs a compressed layer from a dictionary of relative `TermDelta` runs and tokens.
    /// Deduplicates `TermDeltas` in-memory on-the-fly exactly (with zero collision risk).
    #[must_use]
    pub fn new_compressed(
        nw: usize,
        logw: usize,
        runs: Vec<Vec<TermDelta>>,
        tokens: Vec<u32>,
    ) -> Self {
        let mut db = crate::core::proto::cache::ExactDeltaTableBuilder::new();
        let mut delta_segments = Vec::with_capacity(runs.len());
        for run in runs {
            let mut seg = Vec::with_capacity(run.len());
            for d in run {
                let idx = db.dedup(d.g, d.h[0], d.h[1], d.k_index);
                seg.push(idx);
            }
            delta_segments.push(seg);
        }

        Self::new(nw, logw, db.deltas, delta_segments, tokens)
    }

    #[inline(always)]
    pub fn for_each_delta<MutCb: FnMut(&TermDelta)>(&self, mut cb: MutCb) {
        for &tok in &self.delta_tokens {
            for &d_idx in &self.delta_segments[tok as usize] {
                cb(&self.deltas[d_idx as usize]);
            }
        }
    }

    #[inline(always)]
    #[must_use]
    pub fn nw(&self) -> usize {
        self.nw
    }

    #[inline(always)]
    #[must_use]
    pub fn logw(&self) -> usize {
        self.logw
    }

    #[inline(always)]
    #[must_use]
    pub fn num_segments(&self) -> usize {
        self.delta_segments.len()
    }

    #[inline(always)]
    pub fn for_each_delta_index<MutCb: FnMut(u32)>(&self, mut cb: MutCb) {
        for &tok in &self.delta_tokens {
            for &d_idx in &self.delta_segments[tok as usize] {
                cb(d_idx);
            }
        }
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(in crate::core::proto) fn try_for_each_delta_index<
        E,
        MutCb: FnMut(u32) -> Result<(), E>,
    >(
        &self,
        mut cb: MutCb,
    ) -> Result<(), E> {
        for &tok in &self.delta_tokens {
            for &d_idx in &self.delta_segments[tok as usize] {
                cb(d_idx)?;
            }
        }
        Ok(())
    }

    /// Visit this stream. On an degree-only experiment parent this is the quadratic stream;
    /// `streams()` also exposes its linear and constant children.
    #[inline(always)]
    pub fn for_each_general_term<MutCb: FnMut(Term<F>)>(&self, constants: &[F::E], mut cb: MutCb) {
        let mut prev_g = 0u32;
        let mut prev_h0 = 0u32;
        let mut prev_h1 = 0u32;

        for &tok in &self.delta_tokens {
            for &d_idx in &self.delta_segments[tok as usize] {
                let d = &self.deltas[d_idx as usize];
                let g = prev_g.wrapping_add(d.g);
                let h0 = prev_h0.wrapping_add(d.h[0]);
                let h1 = prev_h1.wrapping_add(d.h[1]);

                prev_g = g;
                prev_h0 = h0;
                prev_h1 = h1;

                cb(Term {
                    k: constants[d.k_index as usize].clone(),
                    g,
                    h0,
                    h1,
                });
            }
        }
    }

    #[inline(always)]
    pub fn try_for_each_general_term<E, MutCb: FnMut(Term<F>) -> Result<(), E>>(
        &self,
        constants: &[F::E],
        mut cb: MutCb,
    ) -> Result<(), E> {
        let mut prev_g = 0u32;
        let mut prev_h0 = 0u32;
        let mut prev_h1 = 0u32;

        for &tok in &self.delta_tokens {
            for &d_idx in &self.delta_segments[tok as usize] {
                let d = &self.deltas[d_idx as usize];
                let g = prev_g.wrapping_add(d.g);
                let h0 = prev_h0.wrapping_add(d.h[0]);
                let h1 = prev_h1.wrapping_add(d.h[1]);

                prev_g = g;
                prev_h0 = h0;
                prev_h1 = h1;

                cb(Term {
                    k: constants[d.k_index as usize].clone(),
                    g,
                    h0,
                    h1,
                })?;
            }
        }
        Ok(())
    }

    #[inline(always)]
    pub fn for_each_term(&self, constants: &[F::E], mut cb: impl FnMut(Term<F>)) {
        self.for_each_general_term(constants, &mut cb);
        if let Some(c) = self.coefficients() {
            c.units.for_each(|g, h0, h1| {
                cb(Term {
                    k: c.one().clone(),
                    g,
                    h0,
                    h1,
                })
            });
            c.negatives.for_each(|g, h0, h1| {
                cb(Term {
                    k: c.minus_one().clone(),
                    g,
                    h0,
                    h1,
                })
            });
            c.assertions.for_each(|g, h0, h1| {
                cb(Term {
                    k: c.zero().clone(),
                    g,
                    h0,
                    h1,
                })
            });
        }
    }
    pub fn try_for_each_term<E>(
        &self,
        constants: &[F::E],
        mut cb: impl FnMut(Term<F>) -> Result<(), E>,
    ) -> Result<(), E> {
        self.try_for_each_general_term(constants, &mut cb)?;
        if let Some(c) = self.coefficients() {
            c.units.try_for_each(|g, h0, h1| {
                cb(Term {
                    k: c.one().clone(),
                    g,
                    h0,
                    h1,
                })
            })?;
            c.negatives.try_for_each(|g, h0, h1| {
                cb(Term {
                    k: c.minus_one().clone(),
                    g,
                    h0,
                    h1,
                })
            })?;
            c.assertions.try_for_each(|g, h0, h1| {
                cb(Term {
                    k: c.zero().clone(),
                    g,
                    h0,
                    h1,
                })
            })?;
        }
        Ok(())
    }

    #[inline(always)]
    pub fn terms(&self, constants: &[F::E]) -> Vec<Term<F>> {
        let mut terms = Vec::with_capacity(self.num_terms());
        self.for_each_term(
            constants,
            #[inline(always)]
            |t| terms.push(t),
        );
        terms
    }

    /// Returns the total number of terms across all macro segments referenced in this layer.
    #[must_use]
    pub fn num_terms(&self) -> usize {
        self.coefficients.as_ref().map_or(0, |c| {
            c.units.num_terms() + c.negatives.num_terms() + c.assertions.num_terms()
        }) + self
            .delta_tokens
            .iter()
            .map(|&tok| self.delta_segments[tok as usize].len())
            .sum::<usize>()
            + self
                .affine
                .iter()
                .flat_map(|a| a.iter())
                .map(Self::num_terms)
                .sum::<usize>()
    }

    /// Computes the exact capacity needed for `hc` and `vc` vectors when constructing an `HQuad`
    /// via `bind_g`.
    ///
    /// When `bind_g` iterates through layer terms, consecutive terms sharing `(h0, h1)` corners
    /// are accumulated in-place rather than allocating new corners. Specifically, after binding
    /// `g`, any term with `(h0, h1) == (0, 0)` following the initial `(0, 0)` state is folded
    /// into the current corner. Thus, each term with `d.h[0] != 0 || d.h[1] != 0` contributes a
    /// new corner (`+1`).
    ///
    /// To avoid scanning the same macro segment repeatedly across long `delta_tokens` sequences,
    /// we precompute the number of such non-zero `h` terms for each unique segment in advance.
    #[must_use]
    pub fn nterms_after_bind_g(&self) -> usize {
        // Precompute the count of terms contributing `d.h[0] != 0 || d.h[1] != 0` for each unique
        // segment.
        let seg_counts: Vec<usize> = self
            .delta_segments
            .iter()
            .map(|seg| {
                seg.iter()
                    .filter(|&&d_idx| {
                        let d = &self.deltas[d_idx as usize];
                        d.h[0] != 0 || d.h[1] != 0
                    })
                    .count()
            })
            .collect();

        let mut total = 0;
        let mut is_first = true;

        for &tok in &self.delta_tokens {
            let seg_idx = tok as usize;
            let seg = &self.delta_segments[seg_idx];
            if seg.is_empty() {
                continue;
            }
            if is_first {
                // `HQuad::bind_g` always initializes and emits at least one corner when binding
                // begins. If the very first term of the layer has `(h0, h1) == (0,
                // 0)`, it is pushed as the initial corner before subsequent
                // non-zero `h` terms are processed, contributing `+1` to capacity.
                let first_d = &self.deltas[seg[0] as usize];
                if first_d.h[0] == 0 && first_d.h[1] == 0 {
                    total += 1;
                }
                is_first = false;
            }
            total += seg_counts[seg_idx];
        }
        total
    }
}

impl<F: SerializableField> fmt::Debug for Layer<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Layer")
            .field("nw", &self.nw)
            .field("logw", &self.logw)
            .field("deltas_len", &self.deltas.len())
            .field("delta_segments_len", &self.delta_segments.len())
            .field("delta_tokens_len", &self.delta_tokens.len())
            .finish()
    }
}

pub fn canonical_term<F: SerializableField>(t: Term<F>) -> Term<F> {
    if t.h1 < t.h0 {
        Term {
            k: t.k,
            g: t.g,
            h0: t.h1,
            h1: t.h0,
        }
    } else {
        t
    }
}

/// Historical Morton ordering required by the legacy compiler and two-hand runtime.
/// The V2 compiler applies its own traversal policy without changing this comparison.
pub fn compare_term<F: SerializableField>(f: &F, t: &Term<F>, s: &Term<F>) -> std::cmp::Ordering {
    crate::util::morton::cmp(t.h0 as usize, t.h1 as usize, s.h0 as usize, s.h1 as usize)
        .then_with(|| t.g.cmp(&s.g))
        .then_with(|| f.to_bytes(&t.k).cmp(&f.to_bytes(&s.k)))
}
