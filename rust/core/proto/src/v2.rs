// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Explicit v2 circuit representation used exclusively by v2.
//!
//! `k` indexes the circuit's coefficient table. Coordinate deltas wrap modulo
//! 2^32; coefficient indices are absolute. Every class owns its compression
//! dictionaries. Empty classes are empty streams, without optional children.
use super::{circuit, fixed::CoefficientClasses, SerializableField};

pub(crate) mod encoding;
#[cfg(test)]
mod import;
pub use encoding::compute_id;
#[cfg(test)]
pub(crate) use import::{quadratic_fixture, quadratic_layer_fixture};

pub struct Circuit<F: SerializableField> {
    pub raw: RawCircuit<F>,
    pub id: circuit::DigestBytes,
    pub coefficient_classes: CoefficientClasses,
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
pub struct QuadraticCoordinates {
    pub g: u32,
    pub l: u32,
    pub r: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct Linear {
    pub g: u32,
    pub l: u32,
    pub k: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct LinearCoordinates {
    pub g: u32,
    pub l: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct Constant {
    pub g: u32,
    pub k: u32,
}
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
pub struct ConstantCoordinates {
    pub g: u32,
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
// Only compression traversal is shared. The numerical bind/evaluation loops
// below this representation are written separately for each concrete class.
macro_rules! traversal {
    ($ty:ty, [$($coordinate:ident),+], [$($index:ident),*]) => {
        impl Stream<$ty> {
            /// Delta-encode absolute terms and intern equal records in one run.
            /// Segmentation can replace the run dictionary without changing order.
            pub fn from_terms(terms: impl IntoIterator<Item = $ty>) -> Self {
                let mut previous = <$ty>::default();
                let mut dictionary = std::collections::HashMap::new();
                let mut deltas = Vec::new();
                let terms = terms.into_iter();
                let mut run = Vec::with_capacity(terms.size_hint().0);
                for term in terms {
                    let mut delta = term;
                    $(delta.$coordinate = term.$coordinate.wrapping_sub(previous.$coordinate);)+
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
            pub fn for_each(&self, mut cb: impl FnMut($ty)) {
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
            pub fn try_for_each<E>(&self, mut cb: impl FnMut($ty) -> Result<(), E>) -> Result<(), E> {
                let mut previous = <$ty>::default();
                for &token in &self.tokens {
                    for &index in &self.segments[token as usize] {
                        let delta = self.deltas[index as usize];
                        $(previous.$coordinate = previous.$coordinate.wrapping_add(delta.$coordinate);)+
                        $(previous.$index = delta.$index;)*
                        cb(previous)?;
                    }
                }
                Ok(())
            }
        }
    }
}
traversal!(Quadratic, [g, l, r], [k]);
traversal!(QuadraticCoordinates, [g, l, r], []);
traversal!(Linear, [g, l], [k]);
traversal!(LinearCoordinates, [g, l], []);
traversal!(Constant, [g], [k]);
traversal!(ConstantCoordinates, [g], []);

#[derive(Clone, Default, Debug)]
pub struct Layer {
    pub nw: usize,
    pub logw: usize,
    pub quadratic: Stream<Quadratic>,
    pub quadratic_one: Stream<QuadraticCoordinates>,
    pub quadratic_minus_one: Stream<QuadraticCoordinates>,
    pub quadratic_assertions: Stream<QuadraticCoordinates>,
    pub linear: Stream<Linear>,
    pub linear_one: Stream<LinearCoordinates>,
    pub linear_minus_one: Stream<LinearCoordinates>,
    pub linear_assertions: Stream<LinearCoordinates>,
    pub constant: Stream<Constant>,
    pub constant_one: Stream<ConstantCoordinates>,
    pub constant_minus_one: Stream<ConstantCoordinates>,
}
impl Layer {
    pub fn nw(&self) -> usize {
        self.nw
    }
    pub fn logw(&self) -> usize {
        self.logw
    }
    pub fn term_breakdown(&self) -> [[usize; 3]; 3] {
        self.term_class_breakdown()
            .map(|[zero, one, minus_one, general]| [zero, one, minus_one + general])
    }
    pub fn num_terms(&self) -> usize {
        self.term_class_breakdown().iter().flatten().sum()
    }
    /// Rows: quadratic, linear, constant. Columns: assertions, one, minus one, general.
    pub fn term_class_breakdown(&self) -> [[usize; 4]; 3] {
        [
            [
                self.quadratic_assertions.num_terms(),
                self.quadratic_one.num_terms(),
                self.quadratic_minus_one.num_terms(),
                self.quadratic.num_terms(),
            ],
            [
                self.linear_assertions.num_terms(),
                self.linear_one.num_terms(),
                self.linear_minus_one.num_terms(),
                self.linear.num_terms(),
            ],
            [
                0,
                self.constant_one.num_terms(),
                self.constant_minus_one.num_terms(),
                self.constant.num_terms(),
            ],
        ]
    }
    pub fn heap_bytes(&self) -> usize {
        self.quadratic.heap_bytes()
            + self.quadratic_one.heap_bytes()
            + self.quadratic_minus_one.heap_bytes()
            + self.quadratic_assertions.heap_bytes()
            + self.linear.heap_bytes()
            + self.linear_one.heap_bytes()
            + self.linear_minus_one.heap_bytes()
            + self.linear_assertions.heap_bytes()
            + self.constant.heap_bytes()
            + self.constant_one.heap_bytes()
            + self.constant_minus_one.heap_bytes()
    }
}
impl<F: SerializableField> Circuit<F> {
    pub fn term_class_breakdown(&self, _: &F) -> [[usize; 4]; 3] {
        let mut counts = [[0; 4]; 3];
        for layer in &self.raw.layers {
            for (out, row) in counts.iter_mut().zip(layer.term_class_breakdown()) {
                for (out, n) in out.iter_mut().zip(row) {
                    *out += n;
                }
            }
        }
        counts
    }
    pub fn heap_bytes(&self) -> usize {
        self.raw.constants.capacity() * std::mem::size_of::<F::E>()
            + self.raw.layers.capacity() * std::mem::size_of::<Layer>()
            + self.raw.layers.iter().map(Layer::heap_bytes).sum::<usize>()
    }
    pub fn term_breakdown(&self, _: &F) -> [[usize; 3]; 3] {
        let mut counts = [[0; 3]; 3];
        for layer in &self.raw.layers {
            for (out, row) in counts.iter_mut().zip(layer.term_breakdown()) {
                for (out, n) in out.iter_mut().zip(row) {
                    *out += n;
                }
            }
        }
        counts
    }
}
