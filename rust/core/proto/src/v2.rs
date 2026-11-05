// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 circuits: quadratic, linear, and constant streams.
//!
//! `k` indexes the circuit's coefficient table. Coordinate deltas wrap modulo
//! 2^32; coefficient indices are absolute, with no reserved entries.
//! Quadratic and linear records whose coefficient is zero are assertions.
use super::SerializableField;

pub(crate) mod encoding;
pub mod reader;
pub mod writer;
pub use reader::CircuitReader;
pub use writer::CircuitWriter;
#[cfg(test)]
#[path = "../tests/v2_fixtures.rs"]
mod fixtures;
pub use encoding::compute_id;
#[cfg(test)]
pub(crate) use fixtures::{quadratic_fixture, quadratic_layer_fixture};

pub struct Circuit<F: SerializableField> {
    pub raw: RawCircuit<F>,
    pub id: super::DigestBytes,
}
pub struct RawCircuit<F: SerializableField> {
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub logv: usize,
    pub constants: Vec<F::E>,
    pub layers: Vec<Layer>,
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct Quadratic {
    pub g: u32,
    pub l: u32,
    pub r: u32,
    pub k: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct Linear {
    pub g: u32,
    pub l: u32,
    pub k: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct Constant {
    pub g: u32,
    pub k: u32,
}

pub use super::stream::Stream;

impl Stream<Quadratic> {
    /// Delta-encode absolute terms and intern equal records in one run.
    /// Segmentation can replace the run dictionary without changing order.
    pub fn from_terms(terms: impl IntoIterator<Item = Quadratic>) -> Self {
        let mut previous = Quadratic::default();
        let mut dictionary = std::collections::HashMap::new();
        let mut deltas = Vec::new();
        let terms = terms.into_iter();
        let mut run = Vec::with_capacity(terms.size_hint().0);
        for term in terms {
            let mut delta = term;
            delta.g = term.g.wrapping_sub(previous.g);
            delta.l = term.l.wrapping_sub(previous.l);
            delta.r = term.r.wrapping_sub(previous.r);
            previous = term;
            let index = *dictionary.entry(delta).or_insert_with(|| {
                let index = deltas.len() as u32;
                deltas.push(delta);
                index
            });
            run.push(index);
        }
        if run.is_empty() {
            return Self::default();
        }
        Self {
            deltas,
            segments: vec![run],
            tokens: vec![0],
        }
    }
    #[inline(always)]
    pub fn for_each(&self, mut cb: impl FnMut(Quadratic)) {
        let result: Result<(), std::convert::Infallible> = self.try_for_each(|t| {
            cb(t);
            Ok(())
        });
        match result {
            Ok(()) => (),
            Err(e) => match e {},
        }
    }
    #[inline(always)]
    pub fn try_for_each<E>(&self, mut cb: impl FnMut(Quadratic) -> Result<(), E>) -> Result<(), E> {
        let mut previous = Quadratic::default();
        for &token in &self.tokens {
            for &index in &self.segments[token as usize] {
                let delta = self.deltas[index as usize];
                previous.g = previous.g.wrapping_add(delta.g);
                previous.l = previous.l.wrapping_add(delta.l);
                previous.r = previous.r.wrapping_add(delta.r);
                previous.k = delta.k;
                cb(previous)?;
            }
        }
        Ok(())
    }
}

impl Stream<Linear> {
    /// Delta-encode absolute terms and intern equal records in one run.
    /// Segmentation can replace the run dictionary without changing order.
    pub fn from_terms(terms: impl IntoIterator<Item = Linear>) -> Self {
        let mut previous = Linear::default();
        let mut dictionary = std::collections::HashMap::new();
        let mut deltas = Vec::new();
        let terms = terms.into_iter();
        let mut run = Vec::with_capacity(terms.size_hint().0);
        for term in terms {
            let mut delta = term;
            delta.g = term.g.wrapping_sub(previous.g);
            delta.l = term.l.wrapping_sub(previous.l);
            previous = term;
            let index = *dictionary.entry(delta).or_insert_with(|| {
                let index = deltas.len() as u32;
                deltas.push(delta);
                index
            });
            run.push(index);
        }
        if run.is_empty() {
            return Self::default();
        }
        Self {
            deltas,
            segments: vec![run],
            tokens: vec![0],
        }
    }
    #[inline(always)]
    pub fn for_each(&self, mut cb: impl FnMut(Linear)) {
        let result: Result<(), std::convert::Infallible> = self.try_for_each(|t| {
            cb(t);
            Ok(())
        });
        match result {
            Ok(()) => (),
            Err(e) => match e {},
        }
    }
    #[inline(always)]
    pub fn try_for_each<E>(&self, mut cb: impl FnMut(Linear) -> Result<(), E>) -> Result<(), E> {
        let mut previous = Linear::default();
        for &token in &self.tokens {
            for &index in &self.segments[token as usize] {
                let delta = self.deltas[index as usize];
                previous.g = previous.g.wrapping_add(delta.g);
                previous.l = previous.l.wrapping_add(delta.l);
                previous.k = delta.k;
                cb(previous)?;
            }
        }
        Ok(())
    }
}

impl Stream<Constant> {
    /// Delta-encode absolute terms and intern equal records in one run.
    /// Segmentation can replace the run dictionary without changing order.
    pub fn from_terms(terms: impl IntoIterator<Item = Constant>) -> Self {
        let mut previous = Constant::default();
        let mut dictionary = std::collections::HashMap::new();
        let mut deltas = Vec::new();
        let terms = terms.into_iter();
        let mut run = Vec::with_capacity(terms.size_hint().0);
        for term in terms {
            let mut delta = term;
            delta.g = term.g.wrapping_sub(previous.g);
            previous = term;
            let index = *dictionary.entry(delta).or_insert_with(|| {
                let index = deltas.len() as u32;
                deltas.push(delta);
                index
            });
            run.push(index);
        }
        if run.is_empty() {
            return Self::default();
        }
        Self {
            deltas,
            segments: vec![run],
            tokens: vec![0],
        }
    }
    #[inline(always)]
    pub fn for_each(&self, mut cb: impl FnMut(Constant)) {
        let result: Result<(), std::convert::Infallible> = self.try_for_each(|t| {
            cb(t);
            Ok(())
        });
        match result {
            Ok(()) => (),
            Err(e) => match e {},
        }
    }
    #[inline(always)]
    pub fn try_for_each<E>(&self, mut cb: impl FnMut(Constant) -> Result<(), E>) -> Result<(), E> {
        let mut previous = Constant::default();
        for &token in &self.tokens {
            for &index in &self.segments[token as usize] {
                let delta = self.deltas[index as usize];
                previous.g = previous.g.wrapping_add(delta.g);
                previous.k = delta.k;
                cb(previous)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Default, Debug)]
pub struct Layer {
    pub nw: usize,
    pub logw: usize,
    pub quadratic: Stream<Quadratic>,
    pub linear: Stream<Linear>,
    pub constant: Stream<Constant>,
    assertions: [usize; 2],
}
impl Layer {
    /// Derive assertion metadata from compressed dictionaries using a cached
    /// zero predicate, without expanding repeated terms.
    pub fn with_assertions(
        nw: usize,
        quadratic: Stream<Quadratic>,
        linear: Stream<Linear>,
        constant: Stream<Constant>,
        is_zero: impl Fn(u32) -> bool,
    ) -> Self {
        fn count<T>(s: &Stream<T>, k: impl Fn(&T) -> u32, is_zero: &impl Fn(u32) -> bool) -> usize {
            let counts: Vec<usize> = s
                .segments
                .iter()
                .map(|segment| {
                    segment
                        .iter()
                        .filter(|&&i| is_zero(k(&s.deltas[i as usize])))
                        .count()
                })
                .collect();
            s.tokens.iter().map(|&i| counts[i as usize]).sum()
        }
        let assertions = [
            count(&quadratic, |t| t.k, &is_zero),
            count(&linear, |t| t.k, &is_zero),
        ];
        Self {
            nw,
            logw: crate::util::ceil_log2(nw),
            quadratic,
            linear,
            constant,
            assertions,
        }
    }
    pub fn nw(&self) -> usize {
        self.nw
    }
    pub fn logw(&self) -> usize {
        self.logw
    }
    pub fn assertion_counts(&self) -> [usize; 2] {
        self.assertions
    }
    pub fn num_terms(&self) -> usize {
        self.quadratic.num_terms() + self.linear.num_terms() + self.constant.num_terms()
    }
}

/// An invocation-owned classification, independent of coefficient-table indices.
/// In characteristic two, one and minus one share the One class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum CoefficientClass {
    General = 0,
    One = 1,
    MinusOne = 2,
    Zero = 3,
}
pub fn classify_constants<F: SerializableField>(
    f: &F,
    constants: &[F::E],
) -> Vec<CoefficientClass> {
    let mut bytes = vec![0; f.serialized_size_bytes()];
    let zero = f.bytes_to_element(&bytes).expect("zero field encoding");
    bytes[0] = 1;
    let one = f.bytes_to_element(&bytes).expect("one field encoding");
    let minus = f
        .bytes_to_element(&f.serialized_mone())
        .expect("minus one field encoding");
    constants
        .iter()
        .map(|k| {
            if *k == zero {
                CoefficientClass::Zero
            } else if *k == one {
                CoefficientClass::One
            } else if *k == minus {
                CoefficientClass::MinusOne
            } else {
                CoefficientClass::General
            }
        })
        .collect()
}
