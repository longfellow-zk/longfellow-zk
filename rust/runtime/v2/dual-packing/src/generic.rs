// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trace-zero packing over a finite extension F/K.
//!
//! The commitment precedes this protocol. Authenticate **both** returned equations
//! against that same commitment. The algebraic fixed-commitment error is 1/|F|;
//! this module does not assert joint zero knowledge or a composed FS bound.
//!
//! Write beta for the packing basis and alpha for its trace-dual basis. Every
//! committed word has unique K-coordinates, even if a dishonest prover never
//! used the packer. The reduction links the sumcheck input claim to those
//! coordinates. For K=GF(2), this is what enforces Boolean circuit inputs;
//! subsequent circuit arithmetic still takes place in the full field F.
//!
//! The equations below implement `Instance.nativeLinearVerify_affine` in
//! `formal/dual-packing/DualPacking/ArtinSchreierBackend.lean`, with pivot zero.
use crate::{
    core::algebra::AlgebraicField,
    runtime::algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
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
pub struct FieldEquation<E> {
    pub constant: E,
    pub words: Vec<E>,
    pub auxiliary: Vec<(usize, E)>,
    pub masks: Vec<E>,
}
impl<E: Clone> FieldEquation<E> {
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
pub use crate::runtime::v2::proto::dual_packing::PackingProof;
/// Committed cells: t_1,...,t_(m-1),r,b. An identity extension uses no cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackingMasks<E> {
    pub(super) cells: Vec<E>,
}
impl<E: Clone> PackingMasks<E> {
    pub fn cells(&self) -> &[E] {
        &self.cells
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

/// Substitute t_0 = sum_(k>0) beta_k*t_k. This leaves coefficients only on
/// committed cells, as in the Lean `Instance.contract_mask` identity.
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
fn field_equations<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    u: &[E<X>],
    a: &E<X>,
    delta: &[E<X>],
    gamma: &[E<X>],
    words: Vec<E<X>>,
) -> [FieldEquation<E<X>>; 2] {
    let f = p.field();
    let basis = p.basis();
    let dual = p.dual();
    let rhs = &c.rhs;
    let sigma_a = p.frobenius(a);
    // First row: -A + r + sum_k delta_k*t_k = 0.
    let mut first = eliminate_dependent(f, basis, delta);
    first.extend([f.one(), f.zero()]);
    let negative_gamma = gamma.iter().map(|g| f.neg(g)).collect::<Vec<_>>();
    let mut second = eliminate_dependent(f, basis, &negative_gamma);
    second.extend([f.zero(), f.mone()]);
    let mut eta = f.zero();
    let mut constant = sigma_a;
    // Second row: sigma(A) - b - sum_k gamma_k*(U_k+t_k)
    //             + sum_i word_coeff_i*word_i - eta*rhs(aux) = 0,
    // where gamma_k=sigma(delta_k) and eta=sum_k gamma_k*alpha_k.
    // Expand the affine target onto its original committed auxiliary cells.
    for ((g, alpha), uk) in gamma.iter().zip(dual).zip(u) {
        f.add(&mut eta, &f.mulf(g, alpha));
        f.sub(&mut constant, &f.mulf(g, uk));
    }
    f.sub(&mut constant, &f.mulf(&eta, &rhs.constant));
    [
        FieldEquation {
            constant: f.neg(a),
            words: Vec::new(),
            auxiliary: Vec::new(),
            masks: first,
        },
        FieldEquation {
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

pub(super) fn direct<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
) -> FieldEquation<E<X>> {
    let f = p.field();
    FieldEquation {
        constant: c.rhs.constant.clone(),
        words: c.weights.iter().map(|r| f.neg(r)).collect(),
        auxiliary: c.rhs.terms.clone(),
        masks: Vec::new(),
    }
}
/// For one block rho_j, compute D_k = sum_j alpha_j*coord_k(rho_j).
/// The trace pairing then gives Tr(sum_i D_ik*word_i) = coord_k(input claim).
/// Missing entries in the last block have zero coefficients, so the unused
/// coordinates of the last word need no separate padding constraints.
pub(super) fn coefficients<X: PackingExtension>(
    p: &PackingParameters<X>,
    row: &[E<X>],
) -> Vec<E<X>> {
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
pub(super) fn validate_u<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
) -> Result<(), String> {
    if u.len() != p.degree() {
        return Err("packing response shape".into());
    }
    if u.iter().any(|x| !p.field().is_zero(&p.trace(x))) {
        return Err("packing response has nonzero trace".into());
    }
    Ok(())
}
pub(super) fn validate_proof<X: PackingExtension>(
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
/// Algebraic verifier for explicit independent uniform challenges. Useful for
/// composition and exhaustive algebra tests; callers must sample after all of U.
/// A successful reconstruction is not authentication: both rows must still be
/// enforced against the commitment fixed before the challenge.
pub fn reconstruct<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    delta: &[E<X>],
) -> Result<Vec<FieldEquation<E<X>>>, String> {
    validate_proof(p, c, proof)?;
    reconstruct_validated(p, c, proof, delta)
}
pub(super) fn reconstruct_validated<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    delta: &[E<X>],
) -> Result<Vec<FieldEquation<E<X>>>, String> {
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
    Ok(field_equations(p, c, u, a, delta, &gamma, words).into())
}
