// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Term records, their stream encodings, layers and coefficient classes.
use super::{SerializableField, Stream};

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
            segments: vec![run].into(),
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
            segments: vec![run].into(),
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
            segments: vec![run].into(),
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
    fn try_for_each<E>(&self, mut cb: impl FnMut(Constant) -> Result<(), E>) -> Result<(), E> {
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

/// One layer's term streams. Assertion counts are not stored: the run time
/// derives them from its own classification of the circuit's constants.
#[derive(Clone, Default, Debug)]
pub struct Layer {
    pub nw: usize,
    pub logw: usize,
    pub quadratic: Stream<Quadratic>,
    pub linear: Stream<Linear>,
    pub constant: Stream<Constant>,
}
impl Layer {
    pub fn new(
        nw: usize,
        quadratic: Stream<Quadratic>,
        linear: Stream<Linear>,
        constant: Stream<Constant>,
    ) -> Self {
        Self {
            nw,
            logw: crate::util::ceil_log2(nw),
            quadratic,
            linear,
            constant,
        }
    }
    pub fn nw(&self) -> usize {
        self.nw
    }
    pub fn logw(&self) -> usize {
        self.logw
    }
    /// The quadratic and linear assertion counts: terms whose coefficient
    /// `classes` (from `classify_constants` over the circuit's constants)
    /// marks as zero. Each distinct segment is counted once, then the
    /// per-segment counts are summed over the tokens. Nothing is stored.
    pub fn assertion_counts(&self, classes: &[CoefficientClass]) -> [usize; 2] {
        fn zeros<T>(s: &Stream<T>, classes: &[CoefficientClass], k: impl Fn(&T) -> u32) -> usize {
            let per_segment: Vec<usize> = s
                .segments
                .iter()
                .map(|segment| {
                    segment
                        .iter()
                        .filter(|&&i| {
                            classes[k(&s.deltas[i as usize]) as usize] == CoefficientClass::Zero
                        })
                        .count()
                })
                .collect();
            s.tokens.iter().map(|&t| per_segment[t as usize]).sum()
        }
        [
            zeros(&self.quadratic, classes, |t| t.k),
            zeros(&self.linear, classes, |t| t.k),
        ]
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
