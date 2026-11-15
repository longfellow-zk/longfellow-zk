// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::RuntimeField,
        random::PrivateRandom,
        v2::{
            proto::sumcheck::{PackedReduction, SumcheckProof, SumcheckProofGeometry},
            sumcheck::bind,
            transcript::Transcript,
        },
    },
};
/// Keep the first three rounds in packed form, then reuse ordinary v2 sumcheck.
/// Pads have the standard v2 layout, including its four terminal cells.
pub(super) fn reduce(
    products: &[Product],
    words: &[E],
    weights: &[E],
    pads: &LayerProof<F>,
    t: &mut TranscriptRef<'_>,
) -> Result<Reduction, String> {
    let count = rounds(products.len())?;
    if pads.rounds.len() != count
        || products
            .iter()
            .any(|p| p.g >= weights.len() || p.l >= words.len() || p.r >= words.len())
    {
        return Err("SIMD witness or pad shape".into());
    }
    let f = F::new();
    let mut total = f.zero_accum();
    for p in products {
        f.mac(
            &mut total,
            &weights[p.g],
            &E::from(words[p.l].to_u128() & words[p.r].to_u128()),
        );
    }
    let mut claim = f.accum_reduce(&total);
    let mut monomials = vec![f.one()];
    let mut messages = Vec::new();
    let mut point = Vec::new();
    for i in 0..3.min(count) {
        let polynomial = packed::packed_round(products, words, weights, &monomials, &f);
        let (message, z, next) = mask_round(polynomial, &pads.rounds[i], claim, t, &f);
        claim = next;
        messages.push(message);
        point.push(z);
        let len = monomials.len();
        for j in 0..len {
            monomials.push(f.mulf(&monomials[j], &z));
        }
    }
    let stride = monomials.len();
    // After three contractions each field entry represents eight lanes.
    // Expand only these contracted tables, rather than all 128 bit entries
    // per shared AND, then finish with the ordinary numerical recurrence.
    let weighted: Vec<_> = (0..128)
        .map(|j| f.mulf(&monomials[j % stride], &E::from(1u128 << j)))
        .collect();
    let mut x = Vec::with_capacity(products.len() * 128 / stride);
    let mut y = Vec::with_capacity(x.capacity());
    for p in products {
        let left = words[p.l].to_u128();
        let right = words[p.r].to_u128();
        for offset in (0..128).step_by(stride) {
            let mut a = f.zero();
            let mut b = f.zero();
            for k in 0..stride {
                a.xor_in_place(&select(monomials[k], left >> (offset + k) & 1));
                b.xor_in_place(&select(weighted[offset + k], right >> (offset + k) & 1));
            }
            x.push(a);
            y.push(f.mulf(&weights[p.g], &b));
        }
    }
    for pad in &pads.rounds[point.len()..] {
        let poly = packed::quad_round_poly(&y, &x, &claim, &f);
        let (message, z, next) = mask_round(poly, pad, claim, t, &f);
        claim = next;
        messages.push(message);
        point.push(z);
        bind(&mut x, &z, &f);
        bind(&mut y, &z, &f);
    }
    if x.len() != 1 || y.len() != 1 || f.mulf(&x[0], &y[0]) != claim {
        return Err("SIMD terminal product".into());
    }
    let cross = f.subf(
        &f.addf(
            &f.mulf(&x[0], &pads.claims[1]),
            &f.mulf(&y[0], &pads.claims[0]),
        ),
        &pads.cross,
    );
    let terminal = transcript::terminal(&cross, t, &f);
    let claims = [
        f.addf(&x[0], &f.mulf(&terminal, &pads.claims[0])),
        f.addf(&y[0], &f.mulf(&terminal, &pads.claims[1])),
    ];
    let alpha = transcript::combine(&claims, t, &f);
    Ok(Reduction {
        messages: LayerProof {
            rounds: messages,
            cross,
            claims,
        },
        challenges: Challenges {
            point,
            alpha,
            terminal,
        },
    })
}
fn mask_round(
    poly: RoundPoly<F>,
    pad: &RoundPoly<F>,
    claim: E,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> (RoundPoly<F>, E, E) {
    let message = RoundPoly {
        coefficients: std::array::from_fn(|i| f.subf(&poly.coefficients[i], &pad.coefficients[i])),
    };
    let z = transcript::round(&message, t, f);
    let z2 = f.mulf(&z, &z);
    let next = f.addf(
        &f.mulf(&z2, &claim),
        &f.addf(
            &f.mulf(&f.subf(&f.one(), &z2), &poly.coefficients[0]),
            &f.mulf(&z, &poly.coefficients[1]),
        ),
    );
    (message, z, next)
}

fn select(x: E, bit: u128) -> E {
    E::from(x.to_u128() & 0u128.wrapping_sub(bit))
}

pub(super) struct Prepared {
    owner: [u8; 32],
    words: Vec<E>,
    pads: LayerProof<F>,
    pub(super) masks: adapter::prover::Masks,
    pub(super) cells: Vec<E>,
}
impl Program {
    /// Sample every native mask before the one packed commitment is made.
    pub(super) fn prepare(
        &self,
        words: Vec<E>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(Prepared, Vec<E>), String> {
        if words.len() != self.real {
            return Err("SIMD packed witness size".into());
        }
        let f = F::new();
        let mut expanded = words.clone();
        if let Some(views) = self.inputs.mapped() {
            expanded.extend(views.expand(&words));
        } else {
            for form in self.inputs.uniform().expect("uniform affine operands") {
                let mut word = if form.constant { u128::MAX } else { 0 };
                for &i in &form.vars {
                    word ^= words[i].to_u128();
                }
                expanded.push(E::from(word));
            }
        }
        let mut output = vec![f.zero(); self.circuit.raw.noutput];
        for (p, gs) in self.products.iter().zip(&self.outputs) {
            let x = E::from(expanded[p.l].to_u128() & expanded[p.r].to_u128());
            for &g in gs {
                output[g].xor_in_place(&x);
            }
        }
        self.circuit.raw.layers[0]
            .linear
            .for_each(|v| output[v.g as usize].xor_in_place(&expanded[v.l as usize]));
        self.circuit.raw.layers[0]
            .constant
            .for_each(|v| output[v.g as usize].xor_in_place(&E::from(u128::MAX)));
        if output.iter().any(|x| *x != f.zero()) {
            return Err("SIMD nonzero circuit residual".into());
        }
        let sn = rng.elt_field(&f);
        let mut suffix = Vec::with_capacity(2 * self.rounds() + 4);
        let round_pads = (0..self.rounds())
            .map(|_| {
                let coefficients = [rng.elt_field(&f), rng.elt_field(&f)];
                suffix.extend(coefficients);
                RoundPoly { coefficients }
            })
            .collect();
        let claims = [rng.elt_field(&f), rng.elt_field(&f)];
        suffix.extend(claims);
        suffix.push(f.mulf(&claims[0], &claims[1]));
        let cross = rng.elt_field(&f);
        suffix.push(cross);
        let pads = LayerProof {
            rounds: round_pads,
            claims,
            cross,
        };
        let masks = adapter::prover::Masks::sample(rng);
        let mut cells = words;
        cells.push(sn);
        cells.extend(suffix);
        cells.extend(masks.cells);
        if cells.len() != self.cell_count() {
            return Err("SIMD mask layout".into());
        }
        let witness = cells.clone();
        Ok((
            Prepared {
                owner: self.id,
                words: expanded,
                pads,
                masks,
                cells,
            },
            witness,
        ))
    }
    /// Return masked messages and native equations for the joint opening.
    pub(super) fn prove(
        &self,
        state: Prepared,
        t: &mut TranscriptRef<'_>,
    ) -> Result<(Proof, Vec<NativeRow>), String> {
        let top = self.top_weights(t);
        let (reduction, mut equations, claim) = self.frontend(&state, top, t)?;
        let (packing, rows) = adapter::prover::prove(
            &self.packing,
            &claim,
            &state.cells[..self.real],
            &state.cells,
            state.masks,
            &self.id,
            t,
        )?;
        equations.extend(self.adapter_rows(rows));
        Ok((
            Proof {
                nonlinear: reduction.nonlinear,
                dot: reduction.dot,
                adapter: packing,
            },
            equations,
        ))
    }
    pub(super) fn frontend(
        &self,
        state: &Prepared,
        top: Vec<E>,
        t: &mut TranscriptRef<'_>,
    ) -> Result<(PackedReduction<F>, Vec<NativeRow>, adapter::Claim), String> {
        if state.owner != self.id || state.cells.len() != self.cell_count() {
            return Err("SIMD prepared owner".into());
        }
        let f = F::new();
        let a = top;
        let weights = self.weights(&a);
        let mut n = f.zero_accum();
        for p in &self.products {
            f.mac(
                &mut n,
                &weights[p.g],
                &E::from(state.words[p.l].to_u128() & state.words[p.r].to_u128()),
            );
        }
        let nonlinear = f.addf(&f.accum_reduce(&n), &state.cells[self.sn()]);
        transcript::nonlinear(nonlinear, t, &f);
        let dot = reduce(&self.products, &state.words, &weights, &state.pads, t)?;
        let mix = self
            .inputs
            .mapped()
            .map(|_| transcript::mapped_linear_mix(t, &f));
        let (first, terminal, claim) =
            self.equations(&a, nonlinear, &dot.messages, &dot.challenges, mix);
        let rows = match first {
            Some(row) => vec![row, terminal],
            None => vec![terminal],
        };
        Ok((
            PackedReduction {
                nonlinear,
                dot: dot.messages,
            },
            rows,
            claim,
        ))
    }
}
impl Program {
    pub fn prove_complete(
        &self,
        words: Vec<E>,
        context: &[u8],
        config: PolygeroConfig,
        rng: &mut impl PrivateRandom,
    ) -> Result<Vec<u8>, String> {
        use crate::runtime::{
            algebra::range_interpolation::BinaryInterpolatorFactory,
            v2::polygero::{JointPolygeroParam, JointPolygeroProver},
        };
        let f = F::new();
        let domain = BinaryInterpolatorFactory::full_field(&f);
        let (participant, geometry) = self.parameter(config, &domain)?;
        let param = JointPolygeroParam::new((participant, ())).map_err(|e| e.to_string())?;
        let (state, cells) = self.prepare(words, rng)?;
        let mut t = self.start(context, config);
        let (joint, root) = JointPolygeroProver::commit(&mut t.bound(&param), &(cells, ()), rng)
            .map_err(|e| e.to_string())?;
        let (reduction, rows) = self.prove(state, &mut t.borrow())?;
        let statements = (self.statement(rows, t.bound(&param).session())?, ());
        let opening = joint
            .prove(&mut t.bound(&param), statements)
            .map_err(|e| e.to_string())?;
        SimdEnvelope {
            root,
            reduction,
            opening,
        }
        .write(self, &geometry, config, t)
    }
}

#[cfg(feature = "mldsa")]
use super::shared::ScalarClaim;
#[cfg(feature = "mldsa")]
use crate::runtime::v2::proto::dual_packing::PackingProof;
#[cfg(feature = "mldsa")]
pub(crate) struct SharedState {
    prepared: Prepared,
    pads: Vec<E>,
}

#[cfg(feature = "mldsa")]
impl Program {
    pub(crate) fn prepare_shared(
        &self,
        words: Vec<E>,
        pads: Vec<E>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(SharedState, Vec<E>), String> {
        let (prepared, mut cells) = self.prepare(words, rng)?;
        cells.extend_from_slice(&pads);
        Ok((SharedState { prepared, pads }, cells))
    }
    pub(crate) fn prove_shared(
        &self,
        state: SharedState,
        scalar: ScalarClaim,
        placements: &[(usize, u8)],
        t: &mut TranscriptRef<'_>,
    ) -> Result<(PackedReduction<F>, PackingProof<E>, Vec<NativeRow>), String> {
        let top = self.top_weights(t);
        let (proof, mut rows, mut claim) = self.frontend(&state.prepared, top, t)?;
        let mut cells = state.prepared.cells;
        cells.extend(state.pads);
        self.combine(&mut claim, scalar, placements, cells.len(), t)?;
        let (packing, equations) = adapter::prover::prove(
            &self.packing,
            &claim,
            &cells[..self.real],
            &cells,
            state.prepared.masks,
            &self.id,
            t,
        )?;
        rows.extend(self.adapter_rows(equations));
        Ok((
            proof,
            PackingProof::TraceZero {
                u: packing.u.to_vec(),
                a: packing.a,
            },
            rows,
        ))
    }
}

use crate::runtime::v2::proto::{
    polygero::{PolygeroConfig, PolygeroGeometry},
    simd::{SimdEnvelope, MAGIC},
};
impl SimdEnvelope {
    pub(super) fn write(
        self,
        p: &Program,
        g: &PolygeroGeometry,
        config: PolygeroConfig,
        t: Transcript,
    ) -> Result<Vec<u8>, String> {
        use crate::core::algebra::SerializableField;
        let f = F::new();
        let mut out = MAGIC.to_vec();
        out.extend(self.root.root.data);
        out.extend(f.to_bytes(&self.reduction.nonlinear));
        SumcheckProof {
            layers: vec![self.reduction.dot],
        }
        .write_to_buf(
            &mut out,
            &SumcheckProofGeometry::new(vec![p.rounds()]).map_err(|e| e.to_string())?,
            &f,
        )
        .map_err(|e| e.to_string())?;
        for x in self
            .reduction
            .adapter
            .u
            .into_iter()
            .chain([self.reduction.adapter.a])
        {
            out.extend(f.to_bytes(&x));
        }
        self.opening
            .write_to_buf::<std::io::Error>(
                &mut out,
                config.t,
                config.n,
                |b, buf| b.0.write_response(buf, g, &f),
                |b, buf| b.0.write_rows(buf, g, &f),
            )
            .map_err(|e| e.to_string())?;
        Ok(t.append_final_seal(out).into_bytes())
    }
}
