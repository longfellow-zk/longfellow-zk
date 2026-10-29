// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Conversion from validated archive layers to concrete v2 streams.
use super::{
    circuit, Circuit, Constant, ConstantCoordinates, Layer, Linear, LinearCoordinates, Quadratic,
    QuadraticCoordinates, RawCircuit, Stream,
};
use crate::core::{
    algebra::AlgebraicField,
    proto::{self as legacy, fixed::UnitTerms, SerializableField},
};

// Archive compatibility is isolated here; sumcheck never sees the old Layer.
// unit-stream experiment–coefficient-policy experiment dictionaries move directly, retaining macro
// sharing. degree-only experiment streams are classified once during import. Legacy quadratic-only
// circuits are rejected.
impl<F: SerializableField + AlgebraicField> circuit::Circuit<F> {
    pub fn into_v2(self, f: &F) -> Result<Circuit<F>, String> {
        self.validate_v2()?;
        let coefficient_classes = self
            .raw
            .layers
            .first()
            .and_then(|l| l.coefficients())
            .map_or(super::CoefficientClasses::ONE, |c| c.classes);
        let circuit::RawCircuit {
            ninput,
            npublic_input,
            noutput,
            logv,
            subfield_boundary,
            constants,
            layers,
        } = self.raw;
        let layers = layers
            .into_iter()
            .map(|l| import_layer(l, &constants, f))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Circuit {
            id: self.id,
            coefficient_classes,
            raw: RawCircuit {
                ninput,
                npublic_input,
                noutput,
                logv,
                subfield_boundary,
                constants,
                layers,
            },
        })
    }
}
fn general<T, F: SerializableField>(
    part: legacy::Layer<F>,
    map: impl Fn(legacy::TermDelta) -> T,
) -> Stream<T> {
    let mut deltas: Vec<T> = part.deltas.into_iter().map(map).collect();
    // In-place collect can retain a 16-byte source allocation when records
    // narrow to 12 or 8 bytes. Release that capacity at the import boundary.
    deltas.shrink_to_fit();
    Stream {
        deltas,
        segments: part.delta_segments,
        tokens: part.delta_tokens,
    }
}
fn qfixed(terms: UnitTerms) -> Result<Stream<QuadraticCoordinates>, String> {
    match terms {
        UnitTerms::Quadratic(s) => Ok(Stream {
            deltas: s
                .deltas
                .into_iter()
                .map(|[g, l, r]| QuadraticCoordinates { g, l, r })
                .collect(),
            segments: s.segments,
            tokens: s.tokens,
        }),
        _ => Err("expected quadratic coordinates".into()),
    }
}
fn lfixed(terms: UnitTerms) -> Result<Stream<LinearCoordinates>, String> {
    match terms {
        UnitTerms::Linear(s) => Ok(Stream {
            deltas: s
                .deltas
                .into_iter()
                .map(|[g, l]| LinearCoordinates { g, l })
                .collect(),
            segments: s.segments,
            tokens: s.tokens,
        }),
        UnitTerms::Constant(s) if s.num_terms() == 0 => Ok(Stream::default()),
        _ => Err("expected linear coordinates".into()),
    }
}
fn cfixed(terms: UnitTerms) -> Result<Stream<ConstantCoordinates>, String> {
    match terms {
        UnitTerms::Constant(s) => Ok(Stream {
            deltas: s
                .deltas
                .into_iter()
                .map(|[g]| ConstantCoordinates { g })
                .collect(),
            segments: s.segments,
            tokens: s.tokens,
        }),
        _ => Err("expected constant coordinates".into()),
    }
}
fn import_layer<F: SerializableField + AlgebraicField>(
    mut q: legacy::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Result<Layer, String> {
    let [mut l, mut c] = *q.affine.take().ok_or("sumcheck v2 requires v2 layers")?;
    let mut out = Layer {
        nw: q.nw,
        logw: q.logw,
        ..Layer::default()
    };
    if q.coefficients.is_none() {
        // degree-only experiment has no class dictionaries; convert through the same canonical
        // coefficient partitioner used by the compiler, outside sumcheck.
        classify(&mut out, &q, &l, &c, constants, f)?;
        return Ok(out);
    }
    let qc = q.coefficients.take().unwrap();
    let lc = l
        .coefficients
        .take()
        .ok_or("missing linear coefficient classes")?;
    let cc = c
        .coefficients
        .take()
        .ok_or("missing constant coefficient classes")?;
    out.quadratic_one = qfixed(qc.units)?;
    out.quadratic_minus_one = qfixed(qc.negatives)?;
    out.quadratic_assertions = qfixed(qc.assertions)?;
    out.linear_one = lfixed(lc.units)?;
    out.linear_minus_one = lfixed(lc.negatives)?;
    out.linear_assertions = lfixed(lc.assertions)?;
    if cc.assertions.num_terms() != 0 {
        return Err("constant assertion stream must be empty".into());
    }
    out.constant_one = cfixed(cc.units)?;
    out.constant_minus_one = cfixed(cc.negatives)?;
    out.quadratic = general(q, |d| Quadratic {
        g: d.g,
        l: d.h[0],
        r: d.h[1],
        k: d.k_index,
    });
    out.linear = general(l, |d| Linear {
        g: d.g,
        l: d.h[0],
        k: d.k_index,
    });
    out.constant = general(c, |d| Constant {
        g: d.g,
        k: d.k_index,
    });
    Ok(out)
}
fn classify<F: SerializableField + AlgebraicField>(
    out: &mut Layer,
    q: &legacy::Layer<F>,
    l: &legacy::Layer<F>,
    c: &legacy::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Result<(), String> {
    // Each class starts its own coordinate accumulators. Build a single run
    // for old degree-only experiment imports; newer archives retain their original runs.
    let one = f.one();
    let mut error = false;
    // Use absolute temporary records, then delta-encode once, avoiding a scan
    // through earlier dictionary entries when partitioning large degree-only experiment inputs.
    let mut previous = [0u32; 3];
    q.for_each_delta(|d| {
        previous[0] = previous[0].wrapping_add(d.g);
        previous[1] = previous[1].wrapping_add(d.h[0]);
        previous[2] = previous[2].wrapping_add(d.h[1]);
        let [g, l, r] = previous;
        let k = d.k_index;
        if f.is_zero(&constants[k as usize]) {
            out.quadratic_assertions
                .deltas
                .push(QuadraticCoordinates { g, l, r });
        } else if constants[k as usize] == one {
            out.quadratic_one
                .deltas
                .push(QuadraticCoordinates { g, l, r });
        } else {
            out.quadratic.deltas.push(Quadratic { g, l, r, k });
        }
    });
    let mut previous = [0u32; 2];
    l.for_each_delta(|d| {
        previous[0] = previous[0].wrapping_add(d.g);
        previous[1] = previous[1].wrapping_add(d.h[0]);
        let (g, l) = (previous[0], previous[1]);
        let k = d.k_index;
        if f.is_zero(&constants[k as usize]) {
            out.linear_assertions
                .deltas
                .push(LinearCoordinates { g, l })
        } else if constants[k as usize] == one {
            out.linear_one.deltas.push(LinearCoordinates { g, l })
        } else {
            out.linear.deltas.push(Linear { g, l, k })
        }
    });
    let mut g = 0u32;
    c.for_each_delta(|d| {
        g = g.wrapping_add(d.g);
        let k = d.k_index;
        if f.is_zero(&constants[k as usize]) {
            error = true
        } else if constants[k as usize] == one {
            out.constant_one.deltas.push(ConstantCoordinates { g })
        } else {
            out.constant.deltas.push(Constant { g, k })
        }
    });
    if error {
        return Err("constant assertions are unsupported".into());
    }
    macro_rules! encode {
        ($stream:expr, $ty:ty, $($coord:ident),+) => {{
            let stream = &mut $stream;
            let mut previous = <$ty>::default();
            for term in &mut stream.deltas {
                let absolute = *term;
                $(term.$coord = absolute.$coord.wrapping_sub(previous.$coord);)+
                previous = absolute;
            }
            if !stream.deltas.is_empty() {
                stream.segments.push((0..stream.deltas.len() as u32).collect());
                stream.tokens.push(0);
            }
        }};
    }
    encode!(out.quadratic, Quadratic, g, l, r);
    encode!(out.quadratic_one, QuadraticCoordinates, g, l, r);
    encode!(out.quadratic_assertions, QuadraticCoordinates, g, l, r);
    encode!(out.linear, Linear, g, l);
    encode!(out.linear_one, LinearCoordinates, g, l);
    encode!(out.linear_assertions, LinearCoordinates, g, l);
    encode!(out.constant, Constant, g);
    encode!(out.constant_one, ConstantCoordinates, g);
    Ok(())
}

/// Build explicit v2 fixtures from older tests' hand-written quadratic tensors.
#[cfg(test)]
pub(crate) fn quadratic_fixture<F: SerializableField + AlgebraicField>(
    mut c: circuit::Circuit<F>,
    f: &F,
) -> Circuit<F> {
    c.raw.layers = c
        .raw
        .layers
        .into_iter()
        .map(|l| {
            if l.affine().is_some() {
                return l;
            }
            let (nw, logw) = (l.nw(), l.logw());
            l.with_affine(
                legacy::Layer::new(nw, logw, vec![], vec![], vec![]),
                legacy::Layer::new(nw, logw, vec![], vec![], vec![]),
            )
        })
        .collect();
    c.into_v2(f).unwrap()
}
#[cfg(test)]
pub(crate) fn quadratic_layer_fixture<F: SerializableField + AlgebraicField>(
    l: legacy::Layer<F>,
    constants: &[F::E],
    f: &F,
) -> Layer {
    let (nw, logw) = (l.nw(), l.logw());
    import_layer(
        l.with_affine(
            legacy::Layer::new(nw, logw, vec![], vec![], vec![]),
            legacy::Layer::new(nw, logw, vec![], vec![], vec![]),
        ),
        constants,
        f,
    )
    .unwrap()
}
