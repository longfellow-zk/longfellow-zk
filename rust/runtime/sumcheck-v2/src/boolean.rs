// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! GF128 kernels selected only by trusted circuit structure and a bit-input contract.
//! Window sizes are explicit experimental choices. They never alter proof bytes.
use super::{dense, quad};
use crate::{
    core::{
        bits::PackedBits,
        proto::v2::{
            Circuit, Constant, Layer, Linear, LinearCoordinates, Quadratic, QuadraticCoordinates,
        },
    },
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            AlgebraicField,
        },
        random::Transcript,
        sumcheck_v2::{
            prover::{self, ProverKernel},
            symbolic::LayerChallenges,
            LayerProof, RoundPoly,
        },
    },
};
pub struct BooleanKernel {
    certified: Vec<bool>,
    window: usize,
}
impl BooleanKernel {
    pub fn new(circuit: &Circuit<F>, window: usize) -> Result<Self, String> {
        if !(1..=4).contains(&window) {
            return Err("Boolean window must be 1 through 4".into());
        }
        let mut domain = vec![true; circuit.raw.ninput];
        let mut certified = vec![false; circuit.raw.layers.len()];
        for (i, layer) in circuit.raw.layers.iter().enumerate().rev() {
            certified[i] = domain.iter().all(|&b| b);
            let noutput = if i == 0 {
                circuit.raw.noutput
            } else {
                circuit.raw.layers[i - 1].nw()
            };
            let mut next = vec![true; noutput];
            layer
                .quadratic
                .for_each(|Quadratic { g, .. }| next[g as usize] = false);
            layer
                .quadratic_one
                .for_each(|QuadraticCoordinates { g, l, r }| {
                    next[g as usize] &= domain[l as usize] && domain[r as usize]
                });
            layer
                .linear
                .for_each(|Linear { g, .. }| next[g as usize] = false);
            layer
                .quadratic_minus_one
                .for_each(|QuadraticCoordinates { g, l, r }| {
                    next[g as usize] &= domain[l as usize] && domain[r as usize]
                });
            layer
                .linear_minus_one
                .for_each(|LinearCoordinates { g, l }| next[g as usize] &= domain[l as usize]);
            layer
                .linear_one
                .for_each(|LinearCoordinates { g, l }| next[g as usize] &= domain[l as usize]);
            layer
                .constant
                .for_each(|Constant { g, .. }| next[g as usize] = false);
            domain = next;
        }
        Ok(Self { certified, window })
    }
    pub fn certified_layers(&self) -> &[bool] {
        &self.certified
    }
}
impl ProverKernel<2, F> for BooleanKernel {
    fn bind_r(
        &self,
        index: usize,
        layer: &Layer,
        constants: &[E],
        a: &[E],
        assertions: &[E],
        w: &[E],
        f: &F,
    ) -> Vec<E> {
        if !self.certified[index] {
            return quad::bind_r(layer, constants, a, assertions, w, f);
        }
        let nq = layer.quadratic_assertions.num_terms();
        assert_eq!(assertions.len(), nq + layer.linear_assertions.num_terms());
        let mut result = vec![f.zero(); w.len()];
        layer.quadratic.for_each(|Quadratic { g, l, r, k }| {
            let coefficient = f.mulf(&a[g as usize], &constants[k as usize]);
            result[l as usize].xor_in_place(&select(coefficient, w[r as usize].to_u128() as u8));
        });
        layer
            .quadratic_one
            .for_each(|QuadraticCoordinates { g, l, r }| {
                result[l as usize]
                    .xor_in_place(&select(a[g as usize], w[r as usize].to_u128() as u8));
            });
        let mut rho = assertions[..nq].iter();
        // In characteristic two the implicit negative coefficient equals one.
        layer
            .quadratic_minus_one
            .for_each(|QuadraticCoordinates { g, l, r }| {
                result[l as usize]
                    .xor_in_place(&select(a[g as usize], w[r as usize].to_u128() as u8));
            });
        layer
            .quadratic_assertions
            .for_each(|QuadraticCoordinates { g: _, l, r }| {
                result[l as usize]
                    .xor_in_place(&select(*rho.next().unwrap(), w[r as usize].to_u128() as u8));
            });
        quad::add_linear(layer, constants, a, &assertions[nq..], &mut result, f);
        result
    }
    fn dot_product(
        &self,
        index: usize,
        w: Vec<E>,
        mut q: Vec<E>,
        pads: &LayerProof<2, F>,
        mut claim: E,
        t: &mut Transcript,
        f: &F,
    ) -> (LayerProof<2, F>, LayerChallenges<E>, E) {
        if !self.certified[index] {
            return prover::prove_dot_product(w, q, pads, claim, t, f);
        }
        let bits = w.iter().map(|x| x.to_u128() != 0).collect::<PackedBits>();
        drop(w);
        let mut rounds = Vec::with_capacity(pads.rounds.len());
        let mut points = Vec::with_capacity(pads.rounds.len());
        let mut monomials = vec![f.one()];
        let count = self.window.min(pads.rounds.len());
        for round in 0..count {
            let poly = mixed_round(&bits, &q, &monomials, &claim, f);
            let (message, z, next) = prover::mask_round(poly, &pads.rounds[round], claim, t, f);
            claim = next;
            rounds.push(message);
            points.push(z);
            dense::bind(&mut q, &z, f);
            let previous = monomials.len();
            for i in 0..previous {
                monomials.push(f.mulf(&monomials[i], &z))
            }
        }
        let mut bound = bind_window(&bits, &monomials, f);
        for round in count..pads.rounds.len() {
            let poly = prover::quad_round_poly(&q, &bound, &claim, f);
            let (message, z, next) = prover::mask_round(poly, &pads.rounds[round], claim, t, f);
            claim = next;
            rounds.push(message);
            points.push(z);
            dense::bind(&mut q, &z, f);
            dense::bind(&mut bound, &z, f);
        }
        prover::finish_dot_product(&bound, &q, pads, claim, rounds, points, t, f)
    }
}
#[inline]
fn select(x: E, bit: u8) -> E {
    E::from(x.to_u128() & 0u128.wrapping_sub(u128::from(bit)))
}
fn bit(bits: &PackedBits, i: usize) -> u8 {
    if i < bits.len() {
        u8::from(bits.get(i))
    } else {
        0
    }
}
/// Accumulate full-field coefficients against secret bits before multiplying by
/// public projective monomials. This uses only 2*2^round full-field products.
fn mixed_round(bits: &PackedBits, q: &[E], monomials: &[E], claim: &E, f: &F) -> RoundPoly<2, F> {
    let width = monomials.len();
    let mut c0 = vec![f.zero(); width];
    let mut p1 = vec![f.zero(); width];
    for pair in 0..q.len().div_ceil(2) {
        let even = q[2 * pair];
        let odd = q.get(2 * pair + 1).copied().unwrap_or_default();
        let sum = f.addf(&even, &odd);
        for j in 0..width {
            let b0 = bit(bits, (2 * pair) * width + j);
            let b1 = bit(bits, (2 * pair + 1) * width + j);
            c0[j].xor_in_place(&select(even, b0));
            p1[j].xor_in_place(&select(sum, b0 ^ b1));
        }
    }
    let mut x = f.zero();
    let mut y = f.zero();
    for j in 0..width {
        f.add(&mut x, &f.mulf(&c0[j], &monomials[j]));
        f.add(&mut y, &f.mulf(&p1[j], &monomials[j]));
    }
    RoundPoly {
        coefficients: [x, f.addf(&y, claim)],
    }
}
fn bind_window(bits: &PackedBits, monomials: &[E], f: &F) -> Vec<E> {
    (0..bits.len().div_ceil(monomials.len()))
        .map(|block| {
            let mut x = f.zero();
            for (j, &m) in monomials.iter().enumerate() {
                x.xor_in_place(&select(m, bit(bits, block * monomials.len() + j)))
            }
            x
        })
        .collect()
}

enum LayerWitness {
    Field(Vec<E>),
    Bits(PackedBits),
}
impl LayerWitness {
    fn into_fields(self) -> Vec<E> {
        match self {
            Self::Field(v) => v,
            Self::Bits(bits) => (0..bits.len())
                .map(|i| E::from(u128::from(bits.get(i))))
                .collect(),
        }
    }
}
/// Save certified layers as bits during evaluation, retaining fields only where
/// the circuit's public structure cannot establish a Boolean domain.
pub(crate) fn prove_core(
    mut w: Vec<E>,
    pads: &super::SumcheckProof<2, F>,
    c: &Circuit<F>,
    t: &mut Transcript,
    f: &F,
    window: usize,
) -> Result<(super::SumcheckProof<2, F>, super::symbolic::Constraints<E>), String> {
    let kernel = BooleanKernel::new(c, window)?;
    let mut saved = Vec::with_capacity(c.raw.layers.len());
    for (i, layer) in c.raw.layers.iter().enumerate().rev() {
        let nout = if i == 0 {
            c.raw.noutput
        } else {
            c.raw.layers[i - 1].nw()
        };
        let next = super::eval::eval_layer(&w, layer, &c.raw.constants, nout, f)?;
        saved.push(if kernel.certified[i] {
            LayerWitness::Bits(w.iter().map(|x| x.to_u128() != 0).collect())
        } else {
            LayerWitness::Field(w)
        });
        w = next;
    }
    if w.iter().any(|x| *x != f.zero()) {
        return Err("Boolean circuit output is nonzero".into());
    }
    saved.reverse();
    Ok(prover::prove_core_with_kernel(
        saved.into_iter().map(LayerWitness::into_fields),
        pads,
        c,
        t,
        f,
        &kernel,
    ))
}

#[cfg(test)]
#[path = "../tests/boolean.rs"]
mod tests;
