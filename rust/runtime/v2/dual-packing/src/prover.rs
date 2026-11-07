// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    generic::*,
    transcript::{begin, challenges, finish},
};
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::packing::{AmbientElement as E, BaseElement, PackingExtension, PackingParameters},
        v2::transcript::TranscriptRef,
    },
};
impl<E: Clone> PackingMasks<E> {
    /// Honest setup sets b=sigma(r). The verifier deliberately does not add a
    /// product constraint for this relation. If b is dishonest, sigma(r)-b is
    /// still a fixed offset before delta; the Lean linear soundness theorem
    /// counts solutions to that affine equation with the same 1/|F| bound.
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
}
pub fn prove<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    values: &[BaseElement<X>],
    aux: &[E<X>],
    masks: PackingMasks<E<X>>,
    context: &[u8],
    ts: &mut TranscriptRef<'_>,
) -> Result<(PackingProof<E<X>>, Vec<FieldEquation<E<X>>>), String>
where
    X::Ambient: SerializableField,
{
    if values.len() != c.weights.len() {
        return Err("packing witness shape".into());
    }
    if p.degree() == 1 {
        return prove_packed(p, c, &[], aux, masks, context, ts);
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
    ts: &mut TranscriptRef<'_>,
) -> Result<(PackingProof<E<X>>, Vec<FieldEquation<E<X>>>), String>
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
    // t_0 is dependent, not an extra commitment cell. PackingParameters checks
    // that {1,beta_1,...,beta_(m-1)} is a basis for this mask construction.
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
    // U_k = B_k - alpha_k*target + sigma(t_k)-t_k.
    // Frobenius differences have zero trace, and an honest input claim makes
    // the first two terms' traces cancel coordinate by coordinate.
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
    finish(p, &a, ts);
    let proof = PackingProof::TraceZero { u, a };
    let eq = reconstruct_validated(p, c, &proof, &delta)?;
    Ok((proof, eq))
}
