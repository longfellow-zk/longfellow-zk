// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 circuits: quadratic, linear, and constant streams.
//!
//! `k` indexes the circuit's coefficient table. Coordinate deltas wrap modulo
//! 2^32; coefficient indices are absolute. Entries 0, 1, and 2 are zero, one, and minus one.
//! Quadratic and linear records with k=0 are assertions, not output contributions.
use super::{circuit, SerializableField};

pub(crate) mod encoding;
#[cfg(test)]
mod fixtures;
pub use encoding::compute_id;
#[cfg(test)]
pub(crate) use fixtures::{quadratic_fixture, quadratic_layer_fixture};

pub struct Circuit<F: SerializableField> {
    pub raw: RawCircuit<F>,
    pub id: circuit::DigestBytes,
}
impl<F: SerializableField> Circuit<F> {
    pub fn validate_v2(&self) -> Result<(), String> {
        if self.raw.subfield_boundary != 0 {
            return Err("V2 requires subfield_boundary = 0".into());
        }
        Ok(())
    }
}
pub type RawCircuit<F> = circuit::RawCircuit<F, Layer>;

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

#[derive(Clone, Debug)]
pub struct Stream<T> {
    pub deltas: Vec<T>,
    pub segments: Vec<Vec<u32>>,
    pub tokens: Vec<u32>,
}
impl<T> Default for Stream<T> {
    fn default() -> Self {
        Self {
            deltas: Vec::new(),
            segments: Vec::new(),
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
    pub fn heap_bytes(&self) -> usize {
        self.deltas.capacity() * std::mem::size_of::<T>()
            + self.segments.capacity() * std::mem::size_of::<Vec<u32>>()
            + self
                .segments
                .iter()
                .map(|s| s.capacity() * 4)
                .sum::<usize>()
            + self.tokens.capacity() * 4
    }
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
    /// Derive assertion metadata from compressed dictionaries, without expanding terms.
    pub fn new(
        nw: usize,
        quadratic: Stream<Quadratic>,
        linear: Stream<Linear>,
        constant: Stream<Constant>,
    ) -> Self {
        fn count<T>(s: &Stream<T>, k: impl Fn(&T) -> u32) -> usize {
            let counts: Vec<usize> = s
                .segments
                .iter()
                .map(|segment| {
                    segment
                        .iter()
                        .filter(|&&i| k(&s.deltas[i as usize]) == 0)
                        .count()
                })
                .collect();
            s.tokens.iter().map(|&i| counts[i as usize]).sum()
        }
        let assertions = [count(&quadratic, |t| t.k), count(&linear, |t| t.k)];
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
    pub fn heap_bytes(&self) -> usize {
        self.quadratic.heap_bytes() + self.linear.heap_bytes() + self.constant.heap_bytes()
    }
}
impl<F: SerializableField> Circuit<F> {
    /// Rows: quadratic, linear, constant. Columns: assertions, +1, -1, other.
    /// This is reporting only; coefficients always remain in the three streams.
    pub fn term_class_breakdown(&self, f: &F) -> [[usize; 4]; 3] {
        let mut bytes = vec![0; f.serialized_size_bytes()];
        bytes[0] = 1;
        let one = f.bytes_to_element(&bytes).unwrap();
        let minus = f.bytes_to_element(&f.serialized_mone()).unwrap();
        let mut result = [[0; 4]; 3];
        fn add<T, F: SerializableField>(
            s: &Stream<T>,
            k: impl Fn(&T) -> u32,
            constants: &[F::E],
            one: &F::E,
            minus: &F::E,
            out: &mut [usize; 4],
        ) {
            let mut segments = vec![0usize; s.segments.len()];
            for &i in &s.tokens {
                segments[i as usize] += 1;
            }
            let mut deltas = vec![0usize; s.deltas.len()];
            for (segment, n) in s.segments.iter().zip(segments) {
                for &i in segment {
                    deltas[i as usize] += n;
                }
            }
            for (term, n) in s.deltas.iter().zip(deltas) {
                let k = k(term);
                let class = if k == 0 {
                    0
                } else if constants[k as usize] == *one {
                    1
                } else if constants[k as usize] == *minus {
                    2
                } else {
                    3
                };
                out[class] += n;
            }
        }
        for l in &self.raw.layers {
            add::<_, F>(
                &l.quadratic,
                |t| t.k,
                &self.raw.constants,
                &one,
                &minus,
                &mut result[0],
            );
            add::<_, F>(
                &l.linear,
                |t| t.k,
                &self.raw.constants,
                &one,
                &minus,
                &mut result[1],
            );
            add::<_, F>(
                &l.constant,
                |t| t.k,
                &self.raw.constants,
                &one,
                &minus,
                &mut result[2],
            );
        }
        result
    }
    pub fn term_breakdown(&self, f: &F) -> [[usize; 3]; 3] {
        self.term_class_breakdown(f)
            .map(|[z, o, m, g]| [z, o, m + g])
    }
    pub fn heap_bytes(&self) -> usize {
        self.raw.constants.capacity() * std::mem::size_of::<F::E>()
            + self.raw.layers.capacity() * std::mem::size_of::<Layer>()
            + self.raw.layers.iter().map(Layer::heap_bytes).sum::<usize>()
    }
}

/// The three reserved values are owned by each circuit and implicit in LFC3.
pub(crate) fn implicit_constants<F: SerializableField>(f: &F) -> Result<[F::E; 3], String> {
    let mut bytes = vec![0; f.serialized_size_bytes()];
    if bytes.is_empty() {
        return Err("LFC3 empty field encoding".into());
    }
    let zero = f.bytes_to_element(&bytes)?;
    bytes[0] = 1;
    Ok([
        zero,
        f.bytes_to_element(&bytes)?,
        f.bytes_to_element(&f.serialized_mone())?,
    ])
}
pub(crate) fn validate_constants<F: SerializableField>(
    f: &F,
    constants: &[F::E],
) -> Result<(), String> {
    let implicit = implicit_constants(f)?;
    if constants.get(..3) != Some(implicit.as_slice()) {
        return Err(
            "LFC3 requires implicit coefficients 0, 1, and -1 at indices 0, 1, and 2".into(),
        );
    }
    if constants[3..].iter().any(|k| implicit.contains(k)) {
        return Err("LFC3 implicit coefficient repeated in serialized table".into());
    }
    Ok(())
}
