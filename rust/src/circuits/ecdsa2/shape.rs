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

//! The witness layout of the ECDSA circuit: one field element per entry, in
//! declaration order. The circuit holds a shape of wires, the native witness
//! a shape of field elements; `from_fn` allocates the inputs, `for_each`
//! encodes them in the same order, and `map` converts one into the other.

use crate::circuits::ec::{Pt2, Pt3};

/// The affine points the circuit slices out of its projective sums, and the
/// accumulator after each of the 256 rounds.
#[derive(Clone, Debug)]
pub struct Slicing<T> {
    pub g_pk: Pt2<T>,
    pub g_r: Pt2<T>,
    pub pk_r: Pt2<T>,
    pub g_pk_r: Pt2<T>,
    pub round: [Pt3<T>; 256],
}

/// The key, the digest and the signature `R = (r, y)` with its per-round
/// lookup indices.
#[derive(Clone, Debug)]
pub struct Given<T> {
    pub pkxy: Pt2<T>,
    pub e: T,
    pub rxy: Pt2<T>,
    pub ers: [T; 256],
}

/// The inverses and slicing points the prover supplies.
#[derive(Clone, Debug)]
pub struct Derived<T> {
    pub pkxinv: T,
    pub rxinv: T,
    pub nmsinv: T,
    pub yinv: T,
    pub slicing: Slicing<T>,
}

fn pt2<T>(mut next: impl FnMut() -> T) -> Pt2<T> {
    let x = next();
    (x, next())
}

fn pt3<T>(mut next: impl FnMut() -> T) -> Pt3<T> {
    let x = next();
    let y = next();
    (x, y, next())
}

fn map2<T, U>((x, y): &Pt2<T>, mut f: impl FnMut(&T) -> U) -> Pt2<U> {
    (f(x), f(y))
}

fn map3<T, U>((x, y, z): &Pt3<T>, mut f: impl FnMut(&T) -> U) -> Pt3<U> {
    (f(x), f(y), f(z))
}

impl<T> Slicing<T> {
    pub fn from_fn(mut next: impl FnMut() -> T) -> Self {
        let g_pk = pt2(&mut next);
        let g_r = pt2(&mut next);
        let pk_r = pt2(&mut next);
        let g_pk_r = pt2(&mut next);
        let round = std::array::from_fn(|_| pt3(&mut next));
        Self {
            g_pk,
            g_r,
            pk_r,
            g_pk_r,
            round,
        }
    }

    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        for (x, y) in [&self.g_pk, &self.g_r, &self.pk_r, &self.g_pk_r] {
            f(x);
            f(y);
        }
        for (x, y, z) in &self.round {
            f(x);
            f(y);
            f(z);
        }
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Slicing<U> {
        Slicing {
            g_pk: map2(&self.g_pk, &mut f),
            g_r: map2(&self.g_r, &mut f),
            pk_r: map2(&self.pk_r, &mut f),
            g_pk_r: map2(&self.g_pk_r, &mut f),
            round: std::array::from_fn(|i| map3(&self.round[i], &mut f)),
        }
    }
}

impl<T> Given<T> {
    pub fn from_fn(mut next: impl FnMut() -> T) -> Self {
        let pkxy = pt2(&mut next);
        let e = next();
        Self::from_fn_with_key(pkxy, e, next)
    }

    /// A shape whose key and digest are already at hand, for a circuit that
    /// stores them elsewhere; `next` supplies the signature (`rxy`, `ers`).
    pub fn from_fn_with_key(pkxy: Pt2<T>, e: T, mut next: impl FnMut() -> T) -> Self {
        let rxy = pt2(&mut next);
        let ers = std::array::from_fn(|_| next());
        Self { pkxy, e, rxy, ers }
    }

    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        f(&self.pkxy.0);
        f(&self.pkxy.1);
        f(&self.e);
        self.for_each_signature(f);
    }

    /// The entries [`Self::from_fn_with_key`] allocates, in its order.
    pub fn for_each_signature(&self, mut f: impl FnMut(&T)) {
        f(&self.rxy.0);
        f(&self.rxy.1);
        self.ers.iter().for_each(f);
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Given<U> {
        Given {
            pkxy: map2(&self.pkxy, &mut f),
            e: f(&self.e),
            rxy: map2(&self.rxy, &mut f),
            ers: std::array::from_fn(|i| f(&self.ers[i])),
        }
    }
}

impl<T> Derived<T> {
    pub fn from_fn(mut next: impl FnMut() -> T) -> Self {
        let pkxinv = next();
        let rxinv = next();
        let nmsinv = next();
        let yinv = next();
        Self {
            pkxinv,
            rxinv,
            nmsinv,
            yinv,
            slicing: Slicing::from_fn(next),
        }
    }

    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        f(&self.pkxinv);
        f(&self.rxinv);
        f(&self.nmsinv);
        f(&self.yinv);
        self.slicing.for_each(f);
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Derived<U> {
        Derived {
            pkxinv: f(&self.pkxinv),
            rxinv: f(&self.rxinv),
            nmsinv: f(&self.nmsinv),
            yinv: f(&self.yinv),
            slicing: self.slicing.map(f),
        }
    }
}
