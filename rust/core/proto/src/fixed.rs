// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compressed coordinate-only streams with an implicit coefficient.
use super::{Layer, SerializableField, TermDelta};

#[derive(Clone, Debug, Default)]
pub struct FixedStream<const N: usize> {
    pub deltas: Vec<[u32; N]>,
    pub segments: Vec<Vec<u32>>,
    pub tokens: Vec<u32>,
}
impl<const N: usize> FixedStream<N> {
    pub fn num_terms(&self) -> usize {
        self.tokens
            .iter()
            .map(|&t| self.segments[t as usize].len())
            .sum()
    }
    pub fn heap_bytes(&self) -> usize {
        self.deltas.capacity() * std::mem::size_of::<[u32; N]>()
            + self.segments.capacity() * std::mem::size_of::<Vec<u32>>()
            + self
                .segments
                .iter()
                .map(|s| s.capacity() * 4)
                .sum::<usize>()
            + self.tokens.capacity() * 4
    }
    #[inline(always)]
    pub fn for_each(&self, mut cb: impl FnMut([u32; N])) {
        let mut previous = [0u32; N];
        for &token in &self.tokens {
            for &index in &self.segments[token as usize] {
                for (v, d) in previous.iter_mut().zip(self.deltas[index as usize]) {
                    *v = v.wrapping_add(d);
                }
                cb(previous);
            }
        }
    }
    #[inline(always)]
    pub fn try_for_each<E>(&self, mut cb: impl FnMut([u32; N]) -> Result<(), E>) -> Result<(), E> {
        let mut previous = [0u32; N];
        for &token in &self.tokens {
            for &index in &self.segments[token as usize] {
                for (v, d) in previous.iter_mut().zip(self.deltas[index as usize]) {
                    *v = v.wrapping_add(d);
                }
                cb(previous)?;
            }
        }
        Ok(())
    }
    /// Validate translated runs without expanding repeated macro occurrences.
    pub fn validate(&self, limits: [usize; N]) -> Result<(), String> {
        let mut summaries = Vec::with_capacity(self.segments.len());
        for segment in &self.segments {
            let mut end = [0i64; N];
            let mut min = [i64::MAX; N];
            let mut max = [i64::MIN; N];
            for &index in segment {
                for (j, d) in self.deltas[index as usize].iter().enumerate() {
                    end[j] += i64::from(*d as i32);
                    min[j] = min[j].min(end[j]);
                    max[j] = max[j].max(end[j]);
                }
            }
            summaries.push((end, min, max));
        }
        let mut offset = [0i64; N];
        for &token in &self.tokens {
            if self.segments[token as usize].is_empty() {
                continue;
            }
            let (end, min, max) = summaries[token as usize];
            for j in 0..N {
                if offset[j] + min[j] < 0 || offset[j] + max[j] >= limits[j] as i64 {
                    return Err("fixed-coefficient term index out of bounds".into());
                }
                offset[j] += end[j];
            }
        }
        Ok(())
    }
}
#[derive(Debug)]
pub enum UnitTerms {
    Quadratic(FixedStream<3>),
    Linear(FixedStream<2>),
    Constant(FixedStream<1>),
}
impl UnitTerms {
    pub fn num_terms(&self) -> usize {
        match self {
            Self::Quadratic(s) => s.num_terms(),
            Self::Linear(s) => s.num_terms(),
            Self::Constant(s) => s.num_terms(),
        }
    }
    pub fn heap_bytes(&self) -> usize {
        match self {
            Self::Quadratic(s) => s.heap_bytes(),
            Self::Linear(s) => s.heap_bytes(),
            Self::Constant(s) => s.heap_bytes(),
        }
    }
    #[inline(always)]
    pub fn for_each(&self, mut cb: impl FnMut(u32, u32, u32)) {
        match self {
            Self::Quadratic(s) => s.for_each(|[g, l, r]| cb(g, l, r)),
            Self::Linear(s) => s.for_each(|[g, l]| cb(g, l, 0)),
            Self::Constant(s) => s.for_each(|[g]| cb(g, 0, 0)),
        }
    }
    pub fn try_for_each<E>(
        &self,
        mut cb: impl FnMut(u32, u32, u32) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::Quadratic(s) => s.try_for_each(|[g, l, r]| cb(g, l, r)),
            Self::Linear(s) => s.try_for_each(|[g, l]| cb(g, l, 0)),
            Self::Constant(s) => s.try_for_each(|[g]| cb(g, 0, 0)),
        }
    }
    pub fn validate(&self, outputs: usize, nw: usize) -> Result<(), String> {
        match self {
            Self::Quadratic(s) => s.validate([outputs, nw, nw]),
            Self::Linear(s) => s.validate([outputs, nw]),
            Self::Constant(s) => s.validate([outputs]),
        }
    }
    pub fn from_layer<F: SerializableField>(layer: Layer<F>, arity: usize) -> Self {
        let Layer {
            deltas,
            delta_segments: segments,
            delta_tokens: tokens,
            ..
        } = layer;
        match arity {
            2 => Self::Quadratic(FixedStream {
                deltas: deltas.into_iter().map(|d| [d.g, d.h[0], d.h[1]]).collect(),
                segments,
                tokens,
            }),
            1 => Self::Linear(FixedStream {
                deltas: deltas.into_iter().map(|d| [d.g, d.h[0]]).collect(),
                segments,
                tokens,
            }),
            0 => Self::Constant(FixedStream {
                deltas: deltas.into_iter().map(|d| [d.g]).collect(),
                segments,
                tokens,
            }),
            _ => panic!("invalid degree"),
        }
    }
    pub fn to_layer<F: SerializableField>(&self, nw: usize, logw: usize) -> Layer<F> {
        let map = |g, h0, h1| TermDelta {
            g,
            h: [h0, h1],
            k_index: 0,
        };
        let (deltas, segments, tokens) = match self {
            Self::Quadratic(s) => (
                s.deltas.iter().map(|d| map(d[0], d[1], d[2])).collect(),
                s.segments.clone(),
                s.tokens.clone(),
            ),
            Self::Linear(s) => (
                s.deltas.iter().map(|d| map(d[0], d[1], 0)).collect(),
                s.segments.clone(),
                s.tokens.clone(),
            ),
            Self::Constant(s) => (
                s.deltas.iter().map(|d| map(d[0], 0, 0)).collect(),
                s.segments.clone(),
                s.tokens.clone(),
            ),
        };
        Layer::new(nw, logw, deltas, segments, tokens)
    }
}
impl FixedStream<3> {
    pub fn from_layer<F: SerializableField>(layer: Layer<F>) -> Self {
        let UnitTerms::Quadratic(s) = UnitTerms::from_layer(layer, 2) else {
            unreachable!()
        };
        s
    }
    pub fn to_layer<F: SerializableField>(&self, nw: usize, logw: usize) -> Layer<F> {
        Layer::new(
            nw,
            logw,
            self.deltas
                .iter()
                .map(|d| TermDelta {
                    g: d[0],
                    h: [d[1], d[2]],
                    k_index: 0,
                })
                .collect(),
            self.segments.clone(),
            self.tokens.clone(),
        )
    }
}

pub struct FixedCoefficients<F: SerializableField> {
    pub units: UnitTerms,
    pub assertions: UnitTerms,
    one: F::E,
    zero: F::E,
}
impl<F: SerializableField> FixedCoefficients<F> {
    pub fn new(units: UnitTerms, assertions: UnitTerms, f: &F) -> Result<Self, String> {
        // Canonical scalar one/zero in the supported little-endian field encodings.
        let mut bytes = vec![0; f.serialized_size_bytes()];
        if bytes.is_empty() {
            return Err("empty field encoding".into());
        }
        let zero = f.bytes_to_element(&bytes)?;
        bytes[0] = 1;
        let one = f.bytes_to_element(&bytes)?;
        Ok(Self {
            units,
            assertions,
            one,
            zero,
        })
    }
    pub(crate) fn from_values(
        units: UnitTerms,
        assertions: UnitTerms,
        one: F::E,
        zero: F::E,
    ) -> Self {
        Self {
            units,
            assertions,
            one,
            zero,
        }
    }
    pub fn one(&self) -> &F::E {
        &self.one
    }
    pub fn zero(&self) -> &F::E {
        &self.zero
    }
    pub fn heap_bytes(&self) -> usize {
        self.units.heap_bytes() + self.assertions.heap_bytes()
    }
}
