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

//! Convert between v1 quadratic evaluations and the two-element wire message.
//!
//! A round has p(0)+p(1)=claim. The wire stores p(0) and p(pt(2)), allowing
//! p(1)=claim-p(0) to be reconstructed. `pt(2)` is the field's third distinct
//! interpolation point, including in binary fields. Padding adds or subtracts
//! the two transmitted evaluations componentwise.
pub use crate::runtime::algebra::poly::{LagrangeBasis, Poly};
use crate::{
    core::algebra::SerializableField,
    runtime::{algebra::field::RuntimeField, proto::sumcheck_v1::RoundPoly},
};

/// Select the first and third evaluations for the legacy wire message.
pub trait QuadRoundPoly<const W: usize, F: SerializableField> {
    fn to_wire(&self) -> RoundPoly<W, F>;
}

/// Reconstruct the missing evaluation and apply additive message pads.
pub trait QuadWirePoly<const W: usize, F: RuntimeField<W> + SerializableField> {
    fn to_poly(&self, claim: &F::E, f: &F) -> Poly<3, W, F>;
    fn add(&self, other: &Self, f: &F) -> Self;
    fn sub(&self, other: &Self, f: &F) -> Self;
}

impl<const W: usize, F: SerializableField> QuadRoundPoly<W, F> for Poly<3, W, F> {
    fn to_wire(&self) -> RoundPoly<W, F> {
        RoundPoly {
            evaluations: [self.evaluations[0].clone(), self.evaluations[2].clone()],
        }
    }
}

impl<const W: usize, F: RuntimeField<W> + SerializableField> QuadWirePoly<W, F>
    for RoundPoly<W, F>
{
    fn to_poly(&self, claim: &F::E, f: &F) -> Poly<3, W, F> {
        let g0 = &self.evaluations[0];
        let g2 = &self.evaluations[1];
        let g1 = f.subf(claim, g0);
        Poly {
            evaluations: [g0.clone(), g1, g2.clone()],
        }
    }

    fn add(&self, other: &Self, f: &F) -> Self {
        let mut res = self.clone();
        f.add(&mut res.evaluations[0], &other.evaluations[0]);
        f.add(&mut res.evaluations[1], &other.evaluations[1]);
        res
    }

    fn sub(&self, other: &Self, f: &F) -> Self {
        let mut res = self.clone();
        f.sub(&mut res.evaluations[0], &other.evaluations[0]);
        f.sub(&mut res.evaluations[1], &other.evaluations[1]);
        res
    }
}
