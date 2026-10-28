// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Paper-aligned trace-zero packing over any finite extension F/K.
//!
//! The commitment precedes this protocol. Authenticate **both** returned equations
//! against that same commitment. The native fixed-commitment error is 1/|F|;
//! this module does not assert joint zero knowledge or a composed FS bound.
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            packing::{AmbientElement as E, BaseElement, PackingExtension, PackingParameters},
            SupportsSampling,
        },
        random::{RandomEngine, Transcript},
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Affine<E> {
    pub constant: E,
    pub terms: Vec<(usize, E)>,
}
impl<E: Clone> Affine<E> {
    pub fn evaluate<F: AlgebraicField<E = E>>(&self, values: &[E], f: &F) -> Result<E, String> {
        let mut result = self.constant.clone();
        for (i, k) in &self.terms {
            f.add(
                &mut result,
                &f.mulf(k, values.get(*i).ok_or("packing auxiliary index")?),
            );
        }
        Ok(result)
    }
}
/// sum weights[j]*embed(x[j]) = rhs(aux), where x[j] is in K.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceClaim<E> {
    pub weights: Vec<E>,
    pub rhs: Affine<E>,
    pub auxiliary_count: usize,
}
impl<E> SourceClaim<E> {
    pub fn validate(&self) -> Result<(), String> {
        if self
            .rhs
            .terms
            .iter()
            .any(|(i, _)| *i >= self.auxiliary_count)
        {
            Err("packing auxiliary index".into())
        } else {
            Ok(())
        }
    }
}
/// constant + dot(words,packed) + dot(auxiliary,aux) + dot(masks,cells) = 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeEquation<E> {
    pub constant: E,
    pub words: Vec<E>,
    pub auxiliary: Vec<(usize, E)>,
    pub masks: Vec<E>,
}
impl<E: Clone> NativeEquation<E> {
    pub fn residual<F: AlgebraicField<E = E>>(
        &self,
        words: &[E],
        aux: &[E],
        cells: &[E],
        f: &F,
    ) -> Result<E, String> {
        if (!self.words.is_empty() && words.len() != self.words.len())
            || cells.len() != self.masks.len()
        {
            return Err("packing native witness shape".into());
        }
        let mut value = self.constant.clone();
        for (a, x) in self
            .words
            .iter()
            .zip(words)
            .chain(self.masks.iter().zip(cells))
        {
            f.add(&mut value, &f.mulf(a, x));
        }
        for (i, a) in &self.auxiliary {
            f.add(
                &mut value,
                &f.mulf(a, aux.get(*i).ok_or("packing auxiliary index")?),
            );
        }
        Ok(value)
    }
}
pub use crate::runtime::proto::dual_packing::PackingProof;
/// Committed cells: t_1,...,t_(m-1),r,b. An identity extension uses no cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackingMasks<E> {
    cells: Vec<E>,
}
impl<E: Clone> PackingMasks<E> {
    pub fn cells(&self) -> &[E] {
        &self.cells
    }
    /// Honest setup sets b=sigma(r). The verifier deliberately does not add a
    /// product constraint for this relation; arbitrary committed b is covered.
    pub fn sample<X: PackingExtension>(
        p: &PackingParameters<X>,
        mut sample: impl FnMut() -> E,
    ) -> Self
    where
        X::Ambient: AlgebraicField<E = E>,
    {
        if p.degree() == 1 {
            return Self { cells: Vec::new() };
        }
        let mut cells = (1..p.degree()).map(|_| sample()).collect::<Vec<_>>();
        let r = sample();
        cells.push(r.clone());
        cells.push(p.frobenius(&r));
        Self { cells }
    }
    pub fn from_cells<X: PackingExtension>(
        p: &PackingParameters<X>,
        cells: Vec<E>,
    ) -> Result<Self, String>
    where
        X::Ambient: AlgebraicField<E = E>,
    {
        if cells.len() != mask_cell_count(p.degree()) {
            return Err("packing mask shape".into());
        }
        Ok(Self { cells })
    }
}
pub fn mask_cell_count(degree: usize) -> usize {
    if degree == 1 {
        0
    } else {
        degree + 1
    }
}

/// Shared arithmetic kernel also used by the optimized GF128 implementation.
pub(crate) fn eliminate_dependent<F: AlgebraicField>(
    f: &F,
    basis: &[F::E],
    weights: &[F::E],
) -> Vec<F::E> {
    weights
        .iter()
        .skip(1)
        .zip(basis.iter().skip(1))
        .map(|(w, beta)| f.addf(w, &f.mulf(&weights[0], beta)))
        .collect()
}
#[allow(clippy::too_many_arguments)]
pub(crate) fn native_equations<F: AlgebraicField>(
    f: &F,
    basis: &[F::E],
    dual: &[F::E],
    rhs: &Affine<F::E>,
    u: &[F::E],
    a: &F::E,
    delta: &[F::E],
    gamma: &[F::E],
    sigma_a: &F::E,
    words: Vec<F::E>,
) -> [NativeEquation<F::E>; 2] {
    let mut first = eliminate_dependent(f, basis, delta);
    first.extend([f.one(), f.zero()]);
    let negative_gamma = gamma.iter().map(|g| f.neg(g)).collect::<Vec<_>>();
    let mut second = eliminate_dependent(f, basis, &negative_gamma);
    second.extend([f.zero(), f.mone()]);
    let mut eta = f.zero();
    let mut constant = sigma_a.clone();
    for ((g, alpha), uk) in gamma.iter().zip(dual).zip(u) {
        f.add(&mut eta, &f.mulf(g, alpha));
        f.sub(&mut constant, &f.mulf(g, uk));
    }
    f.sub(&mut constant, &f.mulf(&eta, &rhs.constant));
    [
        NativeEquation {
            constant: f.neg(a),
            words: Vec::new(),
            auxiliary: Vec::new(),
            masks: first,
        },
        NativeEquation {
            constant,
            words,
            auxiliary: rhs
                .terms
                .iter()
                .map(|(i, k)| (*i, f.neg(&f.mulf(&eta, k))))
                .collect(),
            masks: second,
        },
    ]
}

fn direct<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
) -> NativeEquation<E<X>> {
    let f = p.field();
    let scale = f.invert(&p.basis()[0]);
    NativeEquation {
        constant: f.neg(&c.rhs.constant),
        words: c.weights.iter().map(|r| f.mulf(r, &scale)).collect(),
        auxiliary: c.rhs.terms.iter().map(|(i, k)| (*i, f.neg(k))).collect(),
        masks: Vec::new(),
    }
}
/// Compute D_ik one public coefficient block at a time, without a stored tensor.
fn coefficients<X: PackingExtension>(p: &PackingParameters<X>, row: &[E<X>]) -> Vec<E<X>> {
    let f = p.field();
    let m = p.degree();
    if let Some(result) = p.native_coefficients(row) {
        return result;
    }
    let mut result = vec![f.zero(); m];
    let mut digits = vec![p.extension().base().zero(); m];
    for (j, r) in row.iter().enumerate() {
        p.coordinates_into(r, &mut digits);
        for (out, digit) in result.iter_mut().zip(&digits) {
            f.add(out, &f.mulf(&p.dual()[j], &p.extension().embed(f, digit)));
        }
    }
    result
}
fn validate_u<X: PackingExtension>(p: &PackingParameters<X>, u: &[E<X>]) -> Result<(), String> {
    if u.len() != p.degree() {
        return Err("packing response shape".into());
    }
    if u.iter().any(|x| !p.field().is_zero(&p.trace(x))) {
        return Err("packing response has nonzero trace".into());
    }
    Ok(())
}
fn validate_proof<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
) -> Result<(), String> {
    c.validate()?;
    match proof {
        PackingProof::Direct if p.degree() == 1 => Ok(()),
        PackingProof::TraceZero { u, .. } if p.degree() > 1 => validate_u(p, u),
        _ => Err("packing response shape".into()),
    }
}
/// Native verifier for explicit independent uniform challenges. Useful for
/// composition and exhaustive algebra tests; callers must sample after U.
pub fn reconstruct<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    delta: &[E<X>],
) -> Result<Vec<NativeEquation<E<X>>>, String> {
    validate_proof(p, c, proof)?;
    reconstruct_validated(p, c, proof, delta)
}
fn reconstruct_validated<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    delta: &[E<X>],
) -> Result<Vec<NativeEquation<E<X>>>, String> {
    if p.degree() == 1 {
        if !delta.is_empty() {
            return Err("identity packing has no challenges".into());
        }
        return Ok(vec![direct(p, c)]);
    }
    if delta.len() != p.degree() {
        return Err("packing challenge shape".into());
    }
    let PackingProof::TraceZero { u, a } = proof else {
        unreachable!()
    };
    let f = p.field();
    let gamma = delta.iter().map(|d| p.frobenius(d)).collect::<Vec<_>>();
    let words = c
        .weights
        .chunks(p.degree())
        .map(|row| {
            let mut w = f.zero();
            for (g, d) in gamma.iter().zip(coefficients(p, row)) {
                f.add(&mut w, &f.mulf(g, &d));
            }
            w
        })
        .collect();
    Ok(native_equations(
        f,
        p.basis(),
        p.dual(),
        &c.rhs,
        u,
        a,
        delta,
        &gamma,
        &p.frobenius(a),
        words,
    )
    .into())
}
fn begin<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
) where
    X::Ambient: SerializableField,
{
    if p.binary128_profile() {
        ts.write_bytes(b"longfellow/dual-packing128/trace-zero/v1");
        ts.write_bytes(context);
        ts.write_bytes(&super::PACKING_BASIS_ID.to_le_bytes());
    } else {
        ts.write_bytes(b"longfellow/dual-packing/generic/trace-zero/v1");
        ts.write_bytes(&p.descriptor());
        ts.write_bytes(context);
    }
    let f = p.field();
    ts.write_elt_field_slice(&c.weights, f);
    ts.write_elt_field(&c.rhs.constant, f);
    ts.write_bytes(&(c.auxiliary_count as u64).to_le_bytes());
    ts.write_bytes(&(c.rhs.terms.len() as u64).to_le_bytes());
    for (i, k) in &c.rhs.terms {
        ts.write_bytes(&(*i as u64).to_le_bytes());
        ts.write_elt_field(k, f);
    }
}
fn challenges<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
    ts: &mut Transcript,
) -> Vec<E<X>>
where
    X::Ambient: SerializableField,
{
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/U"
    } else {
        b"trace-zero/U"
    });
    ts.write_elt_field_slice(u, p.field());
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/independent-delta"
    } else {
        b"trace-zero/independent-delta"
    });
    (0..p.degree())
        .map(|_| p.field().sample(|n| ts.bytes(n)))
        .collect()
}
pub fn verify<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
) -> Result<Vec<NativeEquation<E<X>>>, String>
where
    X::Ambient: SerializableField,
{
    validate_proof(p, c, proof)?;
    if p.degree() == 1 {
        return reconstruct_validated(p, c, proof, &[]);
    }
    let PackingProof::TraceZero { u, a } = proof else {
        unreachable!()
    };
    begin(p, c, context, ts);
    let delta = challenges(p, u, ts);
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/A"
    } else {
        b"trace-zero/A"
    });
    ts.write_elt_field(a, p.field());
    reconstruct_validated(p, c, proof, &delta)
}
pub fn prove<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    values: &[BaseElement<X>],
    aux: &[E<X>],
    masks: PackingMasks<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
) -> Result<(PackingProof<E<X>>, Vec<NativeEquation<E<X>>>), String>
where
    X::Ambient: SerializableField,
{
    if values.len() != c.weights.len() {
        return Err("packing witness shape".into());
    }
    let words = p.pack(values)?;
    prove_packed(p, c, &words, aux, masks, context, ts)
}
/// Prove directly from the originally committed words. Identity uses no words.
pub fn prove_packed<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    words: &[E<X>],
    aux: &[E<X>],
    masks: PackingMasks<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
) -> Result<(PackingProof<E<X>>, Vec<NativeEquation<E<X>>>), String>
where
    X::Ambient: SerializableField,
{
    c.validate()?;
    if (p.degree() > 1 && words.len() != c.weights.len().div_ceil(p.degree()))
        || aux.len() != c.auxiliary_count
        || masks.cells.len() != mask_cell_count(p.degree())
    {
        return Err("packing witness shape".into());
    }
    if p.degree() == 1 {
        let proof = PackingProof::Direct;
        return Ok((proof, vec![direct(p, c)]));
    }
    let f = p.field();
    let m = p.degree();
    let target = c.rhs.evaluate(aux, f)?;
    let mut t = vec![f.zero(); m];
    t[1..].clone_from_slice(&masks.cells[..m - 1]);
    for k in 1..m {
        let v = f.mulf(&p.basis()[k], &t[k]);
        f.add(&mut t[0], &v);
    }
    let mut b = vec![f.zero(); m];
    for (row, word) in c.weights.chunks(m).zip(words) {
        for (component, d) in b.iter_mut().zip(coefficients(p, row)) {
            f.add(component, &f.mulf(&d, word));
        }
    }
    let u = (0..m)
        .map(|k| {
            f.addf(
                &f.subf(&b[k], &f.mulf(&p.dual()[k], &target)),
                &f.subf(&p.frobenius(&t[k]), &t[k]),
            )
        })
        .collect::<Vec<_>>();
    validate_u(p, &u)?;
    begin(p, c, context, ts);
    let delta = challenges(p, &u, ts);
    let mut a = masks.cells[m - 1].clone();
    for (d, mask) in delta.iter().zip(&t) {
        f.add(&mut a, &f.mulf(d, mask));
    }
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/A"
    } else {
        b"trace-zero/A"
    });
    ts.write_elt_field(&a, f);
    let proof = PackingProof::TraceZero { u, a };
    let eq = reconstruct_validated(p, c, &proof, &delta)?;
    Ok((proof, eq))
}
