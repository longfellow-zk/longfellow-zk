// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Fixed segment storage for decoded v2 circuits. Segment ends delimit slices
//! of one contiguous index array; an empty stream allocates neither array.
use std::ops::{Index, IndexMut};

#[derive(Clone, Debug, Default)]
pub struct Segments {
    ends: Vec<u32>,
    indices: Vec<u32>,
}
impl Segments {
    pub fn len(&self) -> usize {
        self.ends.len()
    }
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &[u32]> + DoubleEndedIterator {
        (0..self.len()).map(|i| &self[i])
    }
    pub fn ends(&self) -> &[u32] {
        &self.ends
    }
    pub fn indices(&self) -> &[u32] {
        &self.indices
    }
    pub(crate) fn from_parts(ends: Vec<u32>, indices: Vec<u32>) -> Result<Self, String> {
        if ends.windows(2).any(|w| w[0] > w[1])
            || ends.last().copied().unwrap_or(0) as usize != indices.len()
        {
            return Err("LFC3 invalid segment ends".into());
        }
        Ok(Self { ends, indices })
    }
}
impl From<Vec<Vec<u32>>> for Segments {
    fn from(segments: Vec<Vec<u32>>) -> Self {
        let mut ends = Vec::with_capacity(segments.len());
        let mut indices = Vec::with_capacity(segments.iter().map(Vec::len).sum());
        for segment in segments {
            indices.extend(segment);
            ends.push(u32::try_from(indices.len()).expect("v2 segment indices exceed u32"));
        }
        Self { ends, indices }
    }
}
impl Index<usize> for Segments {
    type Output = [u32];
    fn index(&self, i: usize) -> &Self::Output {
        let start = if i == 0 { 0 } else { self.ends[i - 1] as usize };
        &self.indices[start..self.ends[i] as usize]
    }
}
impl IndexMut<usize> for Segments {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        let start = if i == 0 { 0 } else { self.ends[i - 1] as usize };
        &mut self.indices[start..self.ends[i] as usize]
    }
}

#[derive(Clone, Debug)]
pub struct Stream<T> {
    pub deltas: Vec<T>,
    pub segments: Segments,
    pub tokens: Vec<u32>,
}
impl<T> Default for Stream<T> {
    fn default() -> Self {
        Self {
            deltas: Vec::new(),
            segments: Segments::default(),
            tokens: Vec::new(),
        }
    }
}
impl<T> Stream<T> {
    pub fn num_terms(&self) -> usize {
        self.tokens
            .iter()
            .map(|&t| self.segments[t as usize].len())
            .sum()
    }
}
