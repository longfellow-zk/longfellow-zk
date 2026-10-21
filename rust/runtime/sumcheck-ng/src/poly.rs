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

use crate::proof::RoundPoly;
use core_algebra::SerializableField;
use runtime_algebra::field::RuntimeField;
pub use runtime_algebra::poly::{LagrangeBasis, Poly};

/// Convert a quadratic's three evaluations to its two transmitted evaluations.
pub trait QuadRoundPoly<const W: usize, F: SerializableField> {
    fn to_wire(&self) -> RoundPoly<W, F>;
}

/// Add and subtract pads from the two transmitted evaluations.
pub trait QuadWirePoly<const W: usize, F: RuntimeField<W> + SerializableField> {
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
