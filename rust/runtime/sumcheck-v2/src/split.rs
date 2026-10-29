// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Per-layer coefficient partitioning, private to sumcheck v2.
//!
//! Split stored segment definitions once. Classes keep the source segment IDs
//! and borrow its token array. Every segment advances by the full source delta,
//! including terms belonging to other classes, so no token rewriting is needed.

use std::ops::Range;

use crate::core::proto::v2::{Constant, Layer, Linear, Quadratic, Stream};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct QuadraticCoordinates {
    pub(super) g: u32,
    pub(super) l: u32,
    pub(super) r: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LinearCoordinates {
    pub(super) g: u32,
    pub(super) l: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ConstantCoordinates {
    pub(super) g: u32,
}

pub(super) struct Runs<'a, const N: usize> {
    tokens: &'a [u32],
    advances: Vec<[u32; N]>,
}
pub(super) struct SplitStream<T> {
    records: Vec<T>,
    ranges: Vec<Range<usize>>,
}
impl<T> SplitStream<T> {
    fn with_capacity(records: usize, segments: usize) -> Self {
        Self {
            records: Vec::with_capacity(records),
            ranges: Vec::with_capacity(segments),
        }
    }
    #[cfg(test)]
    fn num_terms<const N: usize>(&self, runs: &Runs<'_, N>) -> usize {
        if self.records.is_empty() {
            0
        } else {
            runs.tokens
                .iter()
                .map(|&i| self.ranges[i as usize].len())
                .sum()
        }
    }
}
// Buffer order: general, one, minus one, assertions.
fn class(k: u32) -> usize {
    match k {
        0 => 3,
        1 => 1,
        2 => 2,
        _ => 0,
    }
}

// Reserve the source's full stored-record count for each class, then emit in one
// pass. No dictionaries are created and no repeated token is expanded.
fn split_quadratic(
    source: &Stream<Quadratic>,
) -> (
    Runs<'_, 3>,
    SplitStream<Quadratic>,
    SplitStream<QuadraticCoordinates>,
    SplitStream<QuadraticCoordinates>,
    SplitStream<QuadraticCoordinates>,
) {
    let capacity = source.segments.iter().map(Vec::len).sum();
    let mut general = SplitStream::with_capacity(capacity, source.segments.len());
    let mut one = SplitStream::with_capacity(capacity, source.segments.len());
    let mut minus = SplitStream::with_capacity(capacity, source.segments.len());
    let mut zero = SplitStream::with_capacity(capacity, source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in &source.segments {
        let starts = [
            general.records.len(),
            one.records.len(),
            minus.records.len(),
            zero.records.len(),
        ];
        let mut position = [0u32; 3];
        let mut previous = [[0u32; 3]; 4];
        for &i in segment {
            let term = source.deltas[i as usize];
            let c = class(term.k);
            position[0] = position[0].wrapping_add(term.g);
            position[1] = position[1].wrapping_add(term.l);
            position[2] = position[2].wrapping_add(term.r);
            let delta = [
                position[0].wrapping_sub(previous[c][0]),
                position[1].wrapping_sub(previous[c][1]),
                position[2].wrapping_sub(previous[c][2]),
            ];
            previous[c] = position;
            match c {
                0 => general.records.push(Quadratic {
                    g: delta[0],
                    l: delta[1],
                    r: delta[2],
                    k: term.k,
                }),
                1 => one.records.push(QuadraticCoordinates {
                    g: delta[0],
                    l: delta[1],
                    r: delta[2],
                }),
                2 => minus.records.push(QuadraticCoordinates {
                    g: delta[0],
                    l: delta[1],
                    r: delta[2],
                }),
                _ => zero.records.push(QuadraticCoordinates {
                    g: delta[0],
                    l: delta[1],
                    r: delta[2],
                }),
            }
        }
        general.ranges.push(starts[0]..general.records.len());
        one.ranges.push(starts[1]..one.records.len());
        minus.ranges.push(starts[2]..minus.records.len());
        zero.ranges.push(starts[3]..zero.records.len());
        advances.push(position);
    }
    (
        Runs {
            tokens: &source.tokens,
            advances,
        },
        general,
        one,
        minus,
        zero,
    )
}

fn split_linear(
    source: &Stream<Linear>,
) -> (
    Runs<'_, 2>,
    SplitStream<Linear>,
    SplitStream<LinearCoordinates>,
    SplitStream<LinearCoordinates>,
    SplitStream<LinearCoordinates>,
) {
    let capacity = source.segments.iter().map(Vec::len).sum();
    let mut general = SplitStream::with_capacity(capacity, source.segments.len());
    let mut one = SplitStream::with_capacity(capacity, source.segments.len());
    let mut minus = SplitStream::with_capacity(capacity, source.segments.len());
    let mut zero = SplitStream::with_capacity(capacity, source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in &source.segments {
        let starts = [
            general.records.len(),
            one.records.len(),
            minus.records.len(),
            zero.records.len(),
        ];
        let mut position = [0u32; 2];
        let mut previous = [[0u32; 2]; 4];
        for &i in segment {
            let term = source.deltas[i as usize];
            let c = class(term.k);
            position[0] = position[0].wrapping_add(term.g);
            position[1] = position[1].wrapping_add(term.l);
            let delta = [
                position[0].wrapping_sub(previous[c][0]),
                position[1].wrapping_sub(previous[c][1]),
            ];
            previous[c] = position;
            match c {
                0 => general.records.push(Linear {
                    g: delta[0],
                    l: delta[1],
                    k: term.k,
                }),
                1 => one.records.push(LinearCoordinates {
                    g: delta[0],
                    l: delta[1],
                }),
                2 => minus.records.push(LinearCoordinates {
                    g: delta[0],
                    l: delta[1],
                }),
                _ => zero.records.push(LinearCoordinates {
                    g: delta[0],
                    l: delta[1],
                }),
            }
        }
        general.ranges.push(starts[0]..general.records.len());
        one.ranges.push(starts[1]..one.records.len());
        minus.ranges.push(starts[2]..minus.records.len());
        zero.ranges.push(starts[3]..zero.records.len());
        advances.push(position);
    }
    (
        Runs {
            tokens: &source.tokens,
            advances,
        },
        general,
        one,
        minus,
        zero,
    )
}

fn split_constant(
    source: &Stream<Constant>,
) -> (
    Runs<'_, 1>,
    SplitStream<Constant>,
    SplitStream<ConstantCoordinates>,
    SplitStream<ConstantCoordinates>,
) {
    let capacity = source.segments.iter().map(Vec::len).sum();
    let mut general = SplitStream::with_capacity(capacity, source.segments.len());
    let mut one = SplitStream::with_capacity(capacity, source.segments.len());
    let mut minus = SplitStream::with_capacity(capacity, source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in &source.segments {
        let starts = [
            general.records.len(),
            one.records.len(),
            minus.records.len(),
        ];
        let mut position = 0u32;
        let mut previous = [0u32; 3];
        for &i in segment {
            let term = source.deltas[i as usize];
            let c = class(term.k);
            assert!(c < 3, "constant zero markers are not circuit terms");
            position = position.wrapping_add(term.g);
            let delta = position.wrapping_sub(previous[c]);
            previous[c] = position;
            match c {
                0 => general.records.push(Constant {
                    g: delta,
                    k: term.k,
                }),
                1 => one.records.push(ConstantCoordinates { g: delta }),
                _ => minus.records.push(ConstantCoordinates { g: delta }),
            }
        }
        general.ranges.push(starts[0]..general.records.len());
        one.ranges.push(starts[1]..one.records.len());
        minus.ranges.push(starts[2]..minus.records.len());
        advances.push([position]);
    }
    (
        Runs {
            tokens: &source.tokens,
            advances,
        },
        general,
        one,
        minus,
    )
}

impl SplitStream<Quadratic> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 3>, mut cb: impl FnMut(Quadratic)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 3];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                position[1] = position[1].wrapping_add(term.l);
                term.l = position[1];
                position[2] = position[2].wrapping_add(term.r);
                term.r = position[2];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
            base[2] = base[2].wrapping_add(advance[2]);
        }
    }
}

impl SplitStream<QuadraticCoordinates> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 3>, mut cb: impl FnMut(QuadraticCoordinates)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 3];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                position[1] = position[1].wrapping_add(term.l);
                term.l = position[1];
                position[2] = position[2].wrapping_add(term.r);
                term.r = position[2];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
            base[2] = base[2].wrapping_add(advance[2]);
        }
    }
}

impl SplitStream<Linear> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 2>, mut cb: impl FnMut(Linear)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 2];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                position[1] = position[1].wrapping_add(term.l);
                term.l = position[1];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
        }
    }
}

impl SplitStream<LinearCoordinates> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 2>, mut cb: impl FnMut(LinearCoordinates)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 2];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                position[1] = position[1].wrapping_add(term.l);
                term.l = position[1];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
        }
    }
}

impl SplitStream<Constant> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 1>, mut cb: impl FnMut(Constant)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 1];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
        }
    }
}

impl SplitStream<ConstantCoordinates> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 1>, mut cb: impl FnMut(ConstantCoordinates)) {
        if self.records.is_empty() {
            return;
        }
        let mut base = [0u32; 1];
        for &token in runs.tokens {
            let mut position = base;
            let range = self.ranges[token as usize].clone();
            for &delta in &self.records[range] {
                let mut term = delta;
                position[0] = position[0].wrapping_add(term.g);
                term.g = position[0];
                cb(term);
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
        }
    }
}

pub(super) struct SplitLayer<'a> {
    pub(super) nw: usize,
    pub(super) logw: usize,
    pub(super) quadratic_runs: Runs<'a, 3>,
    pub(super) linear_runs: Runs<'a, 2>,
    pub(super) constant_runs: Runs<'a, 1>,
    pub(super) quadratic: SplitStream<Quadratic>,
    pub(super) quadratic_one: SplitStream<QuadraticCoordinates>,
    pub(super) quadratic_minus_one: SplitStream<QuadraticCoordinates>,
    pub(super) quadratic_assertions: SplitStream<QuadraticCoordinates>,
    pub(super) linear: SplitStream<Linear>,
    pub(super) linear_one: SplitStream<LinearCoordinates>,
    pub(super) linear_minus_one: SplitStream<LinearCoordinates>,
    pub(super) linear_assertions: SplitStream<LinearCoordinates>,
    pub(super) constant: SplitStream<Constant>,
    pub(super) constant_one: SplitStream<ConstantCoordinates>,
    pub(super) constant_minus_one: SplitStream<ConstantCoordinates>,
    assertions: [usize; 2],
}
impl<'a> SplitLayer<'a> {
    pub(super) fn new(layer: &'a Layer) -> Self {
        let (quadratic_runs, quadratic, quadratic_one, quadratic_minus_one, quadratic_assertions) =
            split_quadratic(&layer.quadratic);
        let (linear_runs, linear, linear_one, linear_minus_one, linear_assertions) =
            split_linear(&layer.linear);
        let (constant_runs, constant, constant_one, constant_minus_one) =
            split_constant(&layer.constant);
        Self {
            nw: layer.nw,
            logw: layer.logw,
            quadratic_runs,
            linear_runs,
            constant_runs,
            quadratic,
            quadratic_one,
            quadratic_minus_one,
            quadratic_assertions,
            linear,
            linear_one,
            linear_minus_one,
            linear_assertions,
            constant,
            constant_one,
            constant_minus_one,
            assertions: layer.assertion_counts(),
        }
    }
    pub(super) fn assertion_counts(&self) -> [usize; 2] {
        self.assertions
    }
}

#[cfg(test)]
#[path = "../tests/reference.rs"]
mod reference;

#[cfg(test)]
#[path = "../tests/split.rs"]
mod tests;
