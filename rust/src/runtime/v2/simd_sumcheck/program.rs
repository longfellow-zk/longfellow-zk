// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! A shared binary QUAD with public affine operands and packed native inputs.
//! Uniform word views retain the original field-linear protocol. Bit-mapped
//! views authenticate their linear and nonlinear source claims in the adapter.
use sha2::{Digest, Sha256};

use super::{views::BitViews, *};
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::v2::{compute_id, Circuit, CircuitWriter, Stream},
    },
    runtime::{
        algebra::{
            packing::{PackingField, PackingParameters},
            range_interpolation::EvaluationDomain,
            RuntimeField,
        },
        v2::{
            polygero::{LinearStatement, Participant, PolygeroLinearTerm, PolygeroParam},
            proto::polygero::{PolygeroConfig, PolygeroGeometry},
            transcript::SessionStamp,
        },
    },
    util::ceil_log2,
};
#[derive(Clone, Debug)]
pub struct AffineInput {
    pub vars: Vec<usize>,
    pub constant: bool,
}
pub(super) enum AffineForms {
    Uniform(Vec<AffineInput>),
    Mapped(BitViews),
}
impl AffineForms {
    fn len(&self) -> usize {
        match self {
            Self::Uniform(forms) => forms.len(),
            Self::Mapped(views) => views.forms.len(),
        }
    }
    pub(super) fn uniform(&self) -> Option<&[AffineInput]> {
        match self {
            Self::Uniform(forms) => Some(forms),
            Self::Mapped(_) => None,
        }
    }
    pub(super) fn mapped(&self) -> Option<&BitViews> {
        match self {
            Self::Mapped(views) => Some(views),
            Self::Uniform(_) => None,
        }
    }
    fn invalid_sources(&self, real: usize) -> bool {
        match self {
            Self::Uniform(forms) => forms.iter().flat_map(|a| &a.vars).any(|&i| i >= real),
            Self::Mapped(views) => views
                .forms
                .iter()
                .flat_map(|a| &a.terms)
                .any(|t| t.word >= real),
        }
    }
}
pub struct Program {
    pub(super) circuit: Circuit<F>,
    pub(super) inputs: AffineForms,
    pub(super) real: usize,
    pub(super) id: [u8; 32],
    pub(super) products: Vec<Product>,
    pub(super) outputs: Vec<Vec<usize>>,
    pub(super) active: Vec<usize>,
    pub(super) positions: Vec<usize>,
    pub(super) linear_support: Vec<usize>,
    pub(super) packing: adapter::Parameters,
}
impl Program {
    /// Build trusted public metadata for one binary residual layer. Every
    /// output is asserted zero; affine operands are computed from the packed
    /// original/advice words and never receive separate commitment cells.
    pub fn new(
        circuit: Circuit<F>,
        real: usize,
        forms: Vec<AffineInput>,
        source: [u8; 32],
    ) -> Result<Self, String> {
        Self::from_inputs(circuit, real, AffineForms::Uniform(forms), source)
    }
    fn from_inputs(
        circuit: Circuit<F>,
        real: usize,
        inputs: AffineForms,
        source: [u8; 32],
    ) -> Result<Self, String> {
        let f = F::new();
        if circuit.raw.npublic_input != 0
            || circuit.raw.layers.len() != 1
            || circuit.raw.noutput == 0
            || circuit.raw.logv != ceil_log2(circuit.raw.noutput)
            || Some(circuit.raw.ninput) != real.checked_add(inputs.len())
            || inputs.invalid_sources(real)
            || circuit
                .raw
                .constants
                .iter()
                .any(|x| *x != f.zero() && *x != f.one())
        {
            return Err("SIMD shared QUAD shape".into());
        }
        let layer = &circuit.raw.layers[0];
        if layer.nw != circuit.raw.ninput {
            return Err("SIMD input layer width".into());
        }
        fn validate_stream<T>(stream: &Stream<T>) -> Result<(), String> {
            if stream
                .tokens
                .iter()
                .any(|&i| i as usize >= stream.segments.len())
                || stream
                    .segments
                    .indices()
                    .iter()
                    .any(|&i| i as usize >= stream.deltas.len())
            {
                return Err("SIMD stream index".into());
            }
            Ok(())
        }
        validate_stream(&layer.quadratic)?;
        validate_stream(&layer.linear)?;
        validate_stream(&layer.constant)?;
        let mut incidences = Vec::new();
        layer.quadratic.try_for_each(|v| {
            if circuit.raw.constants.get(v.k as usize) != Some(&f.one())
                || (v.g as usize) >= circuit.raw.noutput
                || (v.l as usize) >= circuit.raw.ninput
                || (v.r as usize) >= circuit.raw.ninput
            {
                return Err("SIMD QUAD uses zero-output residuals".to_owned());
            }
            let index = incidences.len();
            incidences.push((
                v.l.min(v.r) as usize,
                v.l.max(v.r) as usize,
                index,
                v.g as usize,
            ));
            Ok(())
        })?;
        let mut valid = true;
        layer.linear.for_each(|v| {
            valid &= circuit.raw.constants.get(v.k as usize) == Some(&f.one())
                && (v.g as usize) < circuit.raw.noutput
                && (v.l as usize) < circuit.raw.ninput
        });
        layer.constant.for_each(|v| {
            valid &= circuit.raw.constants.get(v.k as usize) == Some(&f.one())
                && (v.g as usize) < circuit.raw.noutput
        });
        if !valid {
            return Err("SIMD QUAD coefficient or index".into());
        }
        if incidences.is_empty() {
            return Err("SIMD needs a product".into());
        }
        // Sort to group equal operands, then restore first-occurrence order.
        // This gives the original shared-product numbering without a hash table.
        incidences.sort_unstable();
        let mut groups: Vec<(usize, usize, usize, Vec<usize>)> = Vec::new();
        for (l, r, index, g) in incidences {
            if let Some(last) = groups.last_mut().filter(|a| a.1 == l && a.2 == r) {
                last.0 = last.0.min(index);
                last.3.push(g);
            } else {
                groups.push((index, l, r, vec![g]));
            }
        }
        groups.sort_unstable_by_key(|g| g.0);
        let products: Vec<Product> = groups
            .iter()
            .enumerate()
            .map(|(i, g)| Product {
                g: i,
                l: g.1,
                r: g.2,
            })
            .collect();
        let (active, positions, linear_support, outputs) = {
            let mut active: Vec<_> = groups.iter().flat_map(|g| [g.1, g.2]).collect();
            active.sort_unstable();
            active.dedup();
            let mut positions = vec![usize::MAX; circuit.raw.ninput];
            for (i, &wire) in active.iter().enumerate() {
                positions[wire] = i;
            }
            let mut linear_support = Vec::new();
            layer.linear.for_each(|v| linear_support.push(v.l as usize));
            linear_support.sort_unstable();
            linear_support.dedup();
            let outputs = groups.into_iter().map(|g| g.3).collect();
            (active, positions, linear_support, outputs)
        };
        if compute_id(&f, &circuit.raw) != circuit.id {
            return Err("SIMD circuit identifier".into());
        }
        let mut h = Sha256::new();
        match &inputs {
            AffineForms::Uniform(_) => h.update(b"longfellow/simd/affine-quad/GF128/v2"),
            AffineForms::Mapped(_) => h.update(b"longfellow/simd/mapped-affine-quad/GF128/v1"),
        }
        h.update(source);
        h.update(circuit.id);
        h.update((real as u64).to_le_bytes());
        h.update((inputs.len() as u64).to_le_bytes());
        match &inputs {
            AffineForms::Uniform(forms) => {
                for form in forms {
                    h.update([u8::from(form.constant)]);
                    h.update((form.vars.len() as u64).to_le_bytes());
                    for &word in &form.vars {
                        h.update((word as u64).to_le_bytes());
                    }
                }
            }
            AffineForms::Mapped(views) => views.hash_into(&mut h),
        }
        let count = rounds(products.len())?;
        real.checked_add(1 + 2 * count + 4 + MASKS)
            .ok_or("SIMD cell count")?;
        let packing = PackingParameters::new(f.clone(), f.packing_extension())?;
        Ok(Self {
            circuit,
            inputs,
            real,
            id: h.finalize().into(),
            products,
            outputs,
            active,
            positions,
            linear_support,
            packing,
        })
    }
    pub fn input_words(&self) -> usize {
        self.real
    }
    pub fn products(&self) -> usize {
        self.products.len()
    }
    pub fn rounds(&self) -> usize {
        rounds(self.products.len()).expect("validated SIMD shape")
    }
    pub fn cell_count(&self) -> usize {
        self.real + 1 + 2 * self.rounds() + 4 + MASKS
    }
    pub fn statement_id(&self) -> [u8; 32] {
        self.id
    }
    /// Trusted diagnostic metadata including affine operands; not a loader.
    pub fn metadata_bytes(&self) -> Vec<u8> {
        fn number(v: &mut Vec<u8>, mut n: usize) {
            while n >= 128 {
                v.push((n as u8 & 127) | 128);
                n >>= 7;
            }
            v.push(n as u8);
        }
        let mut out = if self.inputs.mapped().is_some() {
            b"SIMDMD02"
        } else {
            b"SIMDMD01"
        }
        .to_vec();
        out.extend(self.id);
        number(&mut out, self.real);
        let circuit = CircuitWriter::new(&F::new()).to_bytes(&self.circuit);
        number(&mut out, circuit.len());
        out.extend(circuit);
        match &self.inputs {
            AffineForms::Uniform(forms) => {
                number(&mut out, forms.len());
                let mut previous = 0i64;
                for form in forms {
                    out.push(form.constant as u8);
                    number(&mut out, form.vars.len());
                    for &word in &form.vars {
                        let delta = word as i64 - previous;
                        previous = word as i64;
                        number(&mut out, ((delta << 1) ^ (delta >> 63)) as usize);
                    }
                }
            }
            AffineForms::Mapped(views) => out.extend(views.metadata_bytes()),
        }
        out
    }

    /// Build a separate mapped-source program. Map zero must be identity;
    /// every other map is a validated public partial bit permutation. The
    /// complete map table and all lane-varying constants bind the program ID.
    pub fn new_with_bit_views(
        circuit: Circuit<F>,
        real: usize,
        maps: Vec<BitPermutation>,
        forms: Vec<BitAffineInput>,
        source: [u8; 32],
    ) -> Result<Self, String> {
        if real == 0 {
            return Err("mapped affine program needs a source word".into());
        }
        Self::from_inputs(
            circuit,
            real,
            AffineForms::Mapped(BitViews::new(real, maps, forms)?),
            source,
        )
    }
}
impl Program {
    pub(super) fn sn(&self) -> usize {
        self.real
    }
    pub(super) fn pads(&self) -> usize {
        self.real + 1
    }
    pub(super) fn masks(&self) -> usize {
        self.real + 1 + 2 * self.rounds() + 4
    }
    pub(super) fn weights(&self, a: &[E]) -> Vec<E> {
        let f = F::new();
        self.outputs
            .iter()
            .map(|gs| gs.iter().fold(f.zero(), |x, &g| f.addf(&x, &a[g])))
            .collect()
    }
    pub(super) fn project_row(&self, row: NativeRow) -> Result<NativeRow, String> {
        let f = F::new();
        let forms = self
            .inputs
            .uniform()
            .ok_or("bit-mapped residual requires the bit-functional adapter")?;
        let mut coeff = vec![f.zero(); self.cell_count()];
        let mut constant = row.constant;
        for (i, k) in row.terms {
            if i < self.real {
                f.add(&mut coeff[i], &k);
            } else if i < self.circuit.raw.ninput {
                let a = &forms[i - self.real];
                if a.constant {
                    f.fma(&mut constant, &k, &E::from(u128::MAX));
                }
                for &j in &a.vars {
                    f.add(&mut coeff[j], &k);
                }
            } else {
                return Err("SIMD virtual equation index".into());
            }
        }
        Ok(NativeRow {
            constant,
            terms: coeff
                .into_iter()
                .enumerate()
                .filter(|(_, k)| *k != f.zero())
                .collect(),
        })
    }
    pub(super) fn equations(
        &self,
        a: &[E],
        nonlinear: E,
        dot: &LayerProof<F>,
        c: &Challenges,
        linear_mix: Option<E>,
    ) -> (Option<NativeRow>, NativeRow, adapter::Claim) {
        let f = F::new();
        let mut linear = vec![f.zero(); self.circuit.raw.ninput];
        let mut constant = nonlinear;
        self.circuit.raw.layers[0]
            .linear
            .for_each(|v| f.add(&mut linear[v.l as usize], &a[v.g as usize]));
        self.circuit.raw.layers[0]
            .constant
            .for_each(|v| f.fma(&mut constant, &a[v.g as usize], &E::from(u128::MAX)));
        let mut first = if self.inputs.mapped().is_none() {
            Some(
                self.project_row(NativeRow {
                    constant,
                    terms: self
                        .linear_support
                        .iter()
                        .map(|&i| (i, linear[i]))
                        .collect(),
                })
                .expect("validated public affine view"),
            )
        } else {
            None
        };
        if let Some(row) = &mut first {
            row.terms.push((self.sn(), f.one()));
        }
        // Native cells are laid out as packed inputs, the nonlinear-sum pad,
        // two pads per round, four terminal pads, then the adapter's 129 cells.
        // In characteristic two the current projective claim obeys
        // C' = z² C + (1+z²)c0 + z c1. Substitute the masked messages to
        // express the entire recurrence as one affine committed-cell equation.
        let mut terms = vec![(self.sn(), f.one())];
        let mut terminal_constant = nonlinear;
        for (i, (m, z)) in dot.rounds.iter().zip(&c.point).enumerate() {
            let z2 = f.mulf(z, z);
            let k = f.addf(&f.one(), &z2);
            for (_, x) in &mut terms {
                f.mul(x, &z2);
            }
            terms.extend([(self.pads() + 2 * i, k), (self.pads() + 2 * i + 1, *z)]);
            terminal_constant = f.addf(
                &f.mulf(&z2, &terminal_constant),
                &f.addf(
                    &f.mulf(&k, &m.coefficients[0]),
                    &f.mulf(z, &m.coefficients[1]),
                ),
            );
        }
        terms.extend([
            (
                self.pads() + 2 * self.rounds() + 2,
                f.mulf(&c.terminal, &c.terminal),
            ),
            (self.pads() + 2 * self.rounds() + 3, c.terminal),
        ]);
        f.fma(&mut terminal_constant, &c.terminal, &dot.cross);
        f.fma(&mut terminal_constant, &dot.claims[0], &dot.claims[1]);
        let terminal = NativeRow {
            constant: terminal_constant,
            terms,
        };
        // Lane bits are the first seven variables. The remaining variables
        // index shared products. This separation leaves two rank-one input
        // functionals, even when many output residuals share the same AND.
        let lane: [E; 128] = monomials(&c.point[..7], 128).try_into().unwrap();
        let gate = monomials(&c.point[7..], self.products.len());
        let weights = self.weights(a);
        let mut x = vec![f.zero(); self.active.len()];
        let mut y = x.clone();
        for (p, m) in self.products.iter().zip(gate) {
            f.add(&mut x[self.positions[p.l]], &m);
            f.fma(
                &mut y[self.positions[p.r]],
                &f.mulf(&c.alpha, &weights[p.g]),
                &m,
            );
        }
        let mut claim = adapter::Claim {
            factors: vec![
                adapter::Factor {
                    words: x,
                    lanes: lane,
                },
                adapter::Factor {
                    words: y,
                    lanes: std::array::from_fn(|j| f.mulf(&lane[j], &E::from(1u128 << j))),
                },
            ],
            rhs: NativeRow {
                constant: f.addf(&dot.claims[0], &f.mulf(&c.alpha, &dot.claims[1])),
                terms: vec![
                    (self.pads() + 2 * self.rounds(), c.terminal),
                    (
                        self.pads() + 2 * self.rounds() + 1,
                        f.mulf(&c.alpha, &c.terminal),
                    ),
                ],
            },
            auxiliary_count: self.cell_count(),
        };
        if let Some(views) = self.inputs.mapped() {
            let mut factors = Vec::new();
            for factor in claim.factors {
                let (pulled, offset) =
                    views.pullback(self.real, &self.active, &factor.words, &factor.lanes);
                factors.extend(pulled);
                f.add(&mut claim.rhs.constant, &offset);
            }
            // A mapped packed-word relation is not GF128-linear in its
            // committed cells. Fold it into the bit-functional adapter after
            // both terminal claims are fixed, with its own fresh challenge.
            let beta = linear_mix.expect("mapped linear residual challenge");
            let linear_weights: Vec<_> = self
                .linear_support
                .iter()
                .map(|&wire| f.mulf(&beta, &linear[wire]))
                .collect();
            let lanes = std::array::from_fn(|j| E::from(1u128 << j));
            let (pulled, offset) =
                views.pullback(self.real, &self.linear_support, &linear_weights, &lanes);
            factors.extend(pulled);
            // A constant-only relation still names its committed source
            // width. Represent its zero functional explicitly for the
            // adapter rather than dropping the source dimension.
            if factors.is_empty() {
                factors.push(adapter::Factor {
                    words: vec![f.zero(); self.real],
                    lanes: [f.zero(); 128],
                });
            }
            claim.factors = factors;
            f.fma(&mut claim.rhs.constant, &beta, &constant);
            f.add(&mut claim.rhs.constant, &offset);
            claim.rhs.terms.push((self.sn(), beta));
        } else {
            let forms = self.inputs.uniform().expect("uniform affine operands");
            for factor in &mut claim.factors {
                let mut words = vec![f.zero(); self.real];
                let mut offset = f.zero();
                for (&i, k) in self.active.iter().zip(&factor.words) {
                    if i < self.real {
                        f.add(&mut words[i], k);
                    } else {
                        let form = &forms[i - self.real];
                        // Here a constant is one in each Boolean coordinate. Its
                        // contribution is offset*sum(lanes), not a packed-word one.
                        if form.constant {
                            f.add(&mut offset, k);
                        }
                        for &j in &form.vars {
                            f.add(&mut words[j], k);
                        }
                    }
                }
                let lane_sum = factor
                    .lanes
                    .iter()
                    .fold(f.zero(), |sum, value| f.addf(&sum, value));
                f.fma(&mut claim.rhs.constant, &lane_sum, &offset);
                factor.words = words;
            }
        }
        (first, terminal, claim)
    }
    pub(super) fn adapter_rows(&self, rows: [adapter::Equation; 2]) -> [NativeRow; 2] {
        rows.map(|row| {
            let mut terms = row.auxiliary;
            terms.extend(row.words.into_iter().enumerate());
            terms.extend(
                row.masks
                    .into_iter()
                    .enumerate()
                    .map(|(i, k)| (self.masks() + i, k)),
            );
            NativeRow {
                constant: row.constant,
                terms,
            }
        })
    }
}
pub(super) fn monomials(point: &[E], n: usize) -> Vec<E> {
    let f = F::new();
    let mut out = vec![f.one()];
    for z in point {
        let k = out.len();
        for i in 0..k {
            out.push(f.mulf(&out[i], z));
        }
    }
    out.truncate(n);
    out
}

impl Program {
    pub(super) fn parameter<'a, D: EvaluationDomain<F>>(
        &self,
        config: PolygeroConfig,
        domain: &'a D,
    ) -> Result<(Participant<'a, F, D>, PolygeroGeometry), String> {
        let parameter =
            PolygeroParam::try_new(self.cell_count(), config, domain).map_err(|e| e.to_string())?;
        let geometry = parameter.geometry();
        let participant = Participant::new(parameter, domain).map_err(|e| e.to_string())?;
        Ok((participant, geometry))
    }
    pub(super) fn statement(
        &self,
        rows: Vec<NativeRow>,
        session: SessionStamp,
    ) -> Result<LinearStatement<E>, String> {
        if rows
            .iter()
            .flat_map(|r| &r.terms)
            .any(|(i, _)| *i >= self.cell_count())
        {
            return Err("SIMD physical equation index".into());
        }
        let mut a = Vec::new();
        let mut b = Vec::new();
        for (c, row) in rows.into_iter().enumerate() {
            b.push(row.constant);
            a.extend(
                row.terms
                    .into_iter()
                    .map(|(w, k)| PolygeroLinearTerm { c, w, k }),
            );
        }
        Ok(LinearStatement { a, b, session })
    }
}
