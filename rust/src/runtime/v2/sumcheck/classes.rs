// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Per-layer coefficient partitioning, private to sumcheck v2.
//!
//! Classify stored segment definitions once. Classes keep the source segment IDs
//! and borrow its token array. Every segment advances by the full source delta,
//! including terms belonging to other classes, so no token rewriting is needed.

use std::ops::Range;

use crate::core::proto::v2::{CoefficientClass, Constant, Layer, Linear, Quadratic, Stream};
#[cfg(test)]
use crate::core::{
    algebra::SerializableField,
    proto::v2::{classify_constants, Circuit},
};

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
pub(super) struct ClassifiedStream<T> {
    records: Vec<T>,
    ranges: Vec<Range<usize>>,
}
impl<T> ClassifiedStream<T> {
    fn with_capacity(records: usize, segments: usize) -> Self {
        Self {
            records: Vec::with_capacity(records),
            ranges: Vec::with_capacity(segments),
        }
    }
}
// Buffer order: general, one, minus one, assertions.
fn class(k: u32, classes: &[CoefficientClass]) -> usize {
    classes[k as usize] as usize
}
/// Test convenience: classify one circuit with its own classes. The
/// protocol classifies through its `Schedule`, which derives the counts once.
#[cfg(test)]
pub(super) fn classify_layers<'a, F: SerializableField + 'a>(
    c: &'a Circuit<F>,
    f: &F,
) -> Vec<ClassifiedLayer<'a>> {
    let classes = classify_constants(f, &c.raw.constants);
    c.raw
        .layers
        .iter()
        .map(|l| ClassifiedLayer::with_classes(l, &classes, l.assertion_counts(&classes)))
        .collect()
}

// Count stored records by class before allocating. Repeated tokens remain
// compressed; only segment definitions are visited by either pass.
fn class_capacities<T>(
    source: &Stream<T>,
    classes: &[CoefficientClass],
    coefficient: impl Fn(&T) -> u32,
) -> [usize; 4] {
    let mut counts = [0; 4];
    for segment in source.segments.iter() {
        for &index in segment {
            counts[class(coefficient(&source.deltas[index as usize]), classes)] += 1;
        }
    }
    counts
}

fn classify_quadratic<'a>(
    source: &'a Stream<Quadratic>,
    classes: &[CoefficientClass],
) -> (
    Runs<'a, 3>,
    ClassifiedStream<Quadratic>,
    ClassifiedStream<QuadraticCoordinates>,
    ClassifiedStream<QuadraticCoordinates>,
    ClassifiedStream<QuadraticCoordinates>,
) {
    let capacities = class_capacities(source, classes, |term| term.k);
    let mut general = ClassifiedStream::with_capacity(capacities[0], source.segments.len());
    let mut one = ClassifiedStream::with_capacity(capacities[1], source.segments.len());
    let mut minus = ClassifiedStream::with_capacity(capacities[2], source.segments.len());
    let mut zero = ClassifiedStream::with_capacity(capacities[3], source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in source.segments.iter() {
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
            let c = class(term.k, classes);
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

fn classify_linear<'a>(
    source: &'a Stream<Linear>,
    classes: &[CoefficientClass],
) -> (
    Runs<'a, 2>,
    ClassifiedStream<Linear>,
    ClassifiedStream<LinearCoordinates>,
    ClassifiedStream<LinearCoordinates>,
    ClassifiedStream<LinearCoordinates>,
) {
    let capacities = class_capacities(source, classes, |term| term.k);
    let mut general = ClassifiedStream::with_capacity(capacities[0], source.segments.len());
    let mut one = ClassifiedStream::with_capacity(capacities[1], source.segments.len());
    let mut minus = ClassifiedStream::with_capacity(capacities[2], source.segments.len());
    let mut zero = ClassifiedStream::with_capacity(capacities[3], source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in source.segments.iter() {
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
            let c = class(term.k, classes);
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

fn classify_constant<'a>(
    source: &'a Stream<Constant>,
    classes: &[CoefficientClass],
) -> (
    Runs<'a, 1>,
    ClassifiedStream<Constant>,
    ClassifiedStream<ConstantCoordinates>,
    ClassifiedStream<ConstantCoordinates>,
) {
    let capacities = class_capacities(source, classes, |term| term.k);
    let mut general = ClassifiedStream::with_capacity(capacities[0], source.segments.len());
    let mut one = ClassifiedStream::with_capacity(capacities[1], source.segments.len());
    let mut minus = ClassifiedStream::with_capacity(capacities[2], source.segments.len());
    let mut advances = Vec::with_capacity(source.segments.len());
    for segment in source.segments.iter() {
        let starts = [
            general.records.len(),
            one.records.len(),
            minus.records.len(),
        ];
        let mut position = 0u32;
        let mut previous = [0u32; 3];
        for &i in segment {
            let term = source.deltas[i as usize];
            let c = class(term.k, classes);
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

impl ClassifiedStream<Quadratic> {
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

impl ClassifiedStream<QuadraticCoordinates> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 3>, mut cb: impl FnMut(QuadraticCoordinates)) {
        let result: Result<(), std::convert::Infallible> = self.try_for_each(runs, |term| {
            cb(term);
            Ok(())
        });
        match result {
            Ok(()) => (),
            Err(e) => match e {},
        }
    }
    #[inline(always)]
    pub(super) fn try_for_each<E>(
        &self,
        runs: &Runs<'_, 3>,
        mut cb: impl FnMut(QuadraticCoordinates) -> Result<(), E>,
    ) -> Result<(), E> {
        if self.records.is_empty() {
            return Ok(());
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
                cb(term)?;
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
            base[2] = base[2].wrapping_add(advance[2]);
        }
        Ok(())
    }
}

impl ClassifiedStream<Linear> {
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

impl ClassifiedStream<LinearCoordinates> {
    #[inline(always)]
    pub(super) fn for_each(&self, runs: &Runs<'_, 2>, mut cb: impl FnMut(LinearCoordinates)) {
        let result: Result<(), std::convert::Infallible> = self.try_for_each(runs, |term| {
            cb(term);
            Ok(())
        });
        match result {
            Ok(()) => (),
            Err(e) => match e {},
        }
    }
    #[inline(always)]
    pub(super) fn try_for_each<E>(
        &self,
        runs: &Runs<'_, 2>,
        mut cb: impl FnMut(LinearCoordinates) -> Result<(), E>,
    ) -> Result<(), E> {
        if self.records.is_empty() {
            return Ok(());
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
                cb(term)?;
            }
            let advance = runs.advances[token as usize];
            base[0] = base[0].wrapping_add(advance[0]);
            base[1] = base[1].wrapping_add(advance[1]);
        }
        Ok(())
    }
}

impl ClassifiedStream<Constant> {
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

impl ClassifiedStream<ConstantCoordinates> {
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

pub(super) struct ClassifiedLayer<'a> {
    pub(super) nw: usize,
    pub(super) quadratic_runs: Runs<'a, 3>,
    pub(super) linear_runs: Runs<'a, 2>,
    pub(super) constant_runs: Runs<'a, 1>,
    pub(super) quadratic: ClassifiedStream<Quadratic>,
    pub(super) quadratic_one: ClassifiedStream<QuadraticCoordinates>,
    pub(super) quadratic_minus_one: ClassifiedStream<QuadraticCoordinates>,
    pub(super) quadratic_assertions: ClassifiedStream<QuadraticCoordinates>,
    pub(super) linear: ClassifiedStream<Linear>,
    pub(super) linear_one: ClassifiedStream<LinearCoordinates>,
    pub(super) linear_minus_one: ClassifiedStream<LinearCoordinates>,
    pub(super) linear_assertions: ClassifiedStream<LinearCoordinates>,
    pub(super) constant: ClassifiedStream<Constant>,
    pub(super) constant_one: ClassifiedStream<ConstantCoordinates>,
    pub(super) constant_minus_one: ClassifiedStream<ConstantCoordinates>,
    assertions: [usize; 2],
}
impl<'a> ClassifiedLayer<'a> {
    /// `assertions` are the layer's counts under `classes`, which the
    /// caller's schedule derived once.
    pub(super) fn with_classes(
        layer: &'a Layer,
        classes: &[CoefficientClass],
        assertions: [usize; 2],
    ) -> Self {
        let (quadratic_runs, quadratic, quadratic_one, quadratic_minus_one, quadratic_assertions) =
            classify_quadratic(&layer.quadratic, classes);
        let (linear_runs, linear, linear_one, linear_minus_one, linear_assertions) =
            classify_linear(&layer.linear, classes);
        let (constant_runs, constant, constant_one, constant_minus_one) =
            classify_constant(&layer.constant, classes);
        Self {
            nw: layer.nw,
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
            assertions,
        }
    }
    pub(super) fn assertion_counts(&self) -> [usize; 2] {
        self.assertions
    }
}

#[cfg(test)]
mod tests;
