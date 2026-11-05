// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test fixtures for tests that share hand-written quadratic tensors with v1.
use super::{Circuit, Constant, Layer, Linear, Quadratic, RawCircuit, Stream};
use crate::core::algebra::{AlgebraicField, SerializableField};

pub(crate) fn quadratic_fixture<F: SerializableField + AlgebraicField>(
    c: crate::core::proto::v1::Circuit<F>,
    f: &F,
) -> Circuit<F> {
    let mut constants = vec![f.zero(), f.one(), f.mone()];
    let mapping: Vec<u32> = c
        .raw
        .constants
        .iter()
        .map(|k| {
            if let Some(i) = constants.iter().position(|x| x == k) {
                i as u32
            } else {
                let i = constants.len() as u32;
                constants.push(k.clone());
                i
            }
        })
        .collect();
    let layers = c
        .raw
        .layers
        .into_iter()
        .map(|l| {
            let mut terms = Vec::new();
            l.for_each_term(&c.raw.constants, |t| terms.push(t));
            let terms = terms.into_iter().map(|t| {
                let old = c.raw.constants.iter().position(|k| *k == t.k).unwrap();
                Quadratic {
                    g: t.g,
                    l: t.h0,
                    r: t.h1,
                    k: mapping[old],
                }
            });
            Layer::new(
                l.nw(),
                Stream::<Quadratic>::from_terms(terms),
                Stream::default(),
                Stream::default(),
            )
        })
        .collect();
    let raw = RawCircuit {
        ninput: c.raw.ninput,
        npublic_input: c.raw.npublic_input,
        noutput: c.raw.noutput,
        logv: c.raw.logv,
        constants,
        layers,
    };
    Circuit {
        id: super::compute_id(f, &raw),
        raw,
    }
}
pub(crate) fn quadratic_layer_fixture<F: SerializableField + AlgebraicField>(
    l: crate::core::proto::v1::Layer<F>,
    constants: &[F::E],
    _f: &F,
) -> Layer {
    let mut previous = [0u32; 3];
    let mut terms = Vec::new();
    l.for_each_delta(|d| {
        previous[0] = previous[0].wrapping_add(d.g);
        previous[1] = previous[1].wrapping_add(d.h[0]);
        previous[2] = previous[2].wrapping_add(d.h[1]);
        assert!((d.k_index as usize) < constants.len());
        terms.push(Quadratic {
            g: previous[0],
            l: previous[1],
            r: previous[2],
            k: d.k_index,
        });
    });
    Layer::new(
        l.nw(),
        Stream::<Quadratic>::from_terms(terms),
        Stream::default(),
        Stream::default(),
    )
}

impl Layer {
    // Compatibility helper for test fixtures with the former table ordering.
    pub(crate) fn new(
        nw: usize,
        quadratic: Stream<Quadratic>,
        linear: Stream<Linear>,
        constant: Stream<Constant>,
    ) -> Self {
        Self::with_assertions(nw, quadratic, linear, constant, |k| k == 0)
    }
}

use super::{classify_constants, CoefficientClass};
impl<F: SerializableField> Circuit<F> {
    /// Rows: quadratic, linear, constant. Columns: assertions, +1, -1, other.
    /// This is reporting only; coefficients always remain in the three streams.
    pub fn term_class_breakdown(&self, f: &F) -> [[usize; 4]; 3] {
        let mut result = [[0; 4]; 3];
        let classes = classify_constants(f, &self.raw.constants);
        fn add<T>(
            s: &Stream<T>,
            k: impl Fn(&T) -> u32,
            out: &mut [usize; 4],
            classes: &[CoefficientClass],
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
                let class = match classes[k as usize] {
                    CoefficientClass::Zero => 0,
                    CoefficientClass::One => 1,
                    CoefficientClass::MinusOne => 2,
                    CoefficientClass::General => 3,
                };
                out[class] += n;
            }
        }
        for l in &self.raw.layers {
            add(&l.quadratic, |t| t.k, &mut result[0], &classes);
            add(&l.linear, |t| t.k, &mut result[1], &classes);
            add(&l.constant, |t| t.k, &mut result[2], &classes);
        }
        result
    }
    pub fn term_breakdown(&self, f: &F) -> [[usize; 3]; 3] {
        self.term_class_breakdown(f)
            .map(|[z, o, m, g]| [z, o, m + g])
    }
}
