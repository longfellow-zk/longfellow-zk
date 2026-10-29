// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test fixtures for tests that share hand-written quadratic tensors with v1.
use super::{circuit, Circuit, Layer, Quadratic, RawCircuit, Stream};
use crate::core::algebra::{AlgebraicField, SerializableField};

pub(crate) fn quadratic_fixture<F: SerializableField + AlgebraicField>(
    c: circuit::Circuit<F>,
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
        subfield_boundary: c.raw.subfield_boundary,
        constants,
        layers,
    };
    Circuit {
        id: super::compute_id(f, &raw),
        raw,
    }
}
pub(crate) fn quadratic_layer_fixture<F: SerializableField + AlgebraicField>(
    l: crate::core::proto::Layer<F>,
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
