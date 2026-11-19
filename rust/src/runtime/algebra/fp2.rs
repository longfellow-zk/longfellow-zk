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

use crate::{
    core::algebra::{AlgebraicField, BareField, SupportsU64Conversions},
    runtime::algebra::{RuntimeField, SupportsQuadraticExtension},
};

pub struct Fp2Element<F: SupportsQuadraticExtension> {
    pub re: F::E,
    pub im: F::E,
}

impl<F: SupportsQuadraticExtension> Clone for Fp2Element<F> {
    fn clone(&self) -> Self {
        Self {
            re: self.re.clone(),
            im: self.im.clone(),
        }
    }
}

impl<F: SupportsQuadraticExtension> Copy for Fp2Element<F> where F::E: Copy {}

impl<F: SupportsQuadraticExtension> std::fmt::Debug for Fp2Element<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Fp2Element")
            .field("re", &self.re)
            .field("im", &self.im)
            .finish()
    }
}

impl<F: SupportsQuadraticExtension> PartialEq for Fp2Element<F> {
    fn eq(&self, other: &Self) -> bool {
        self.re == other.re && self.im == other.im
    }
}

impl<F: SupportsQuadraticExtension> Eq for Fp2Element<F> {}

impl<F: SupportsQuadraticExtension> std::hash::Hash for Fp2Element<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.re.hash(state);
        self.im.hash(state);
    }
}

/// Arithmetic in the quadratic extension `F[i] / (i² + 1)`.
///
/// This field deliberately does not implement serialization. Protocol values
/// must remain in the base field, which has a canonical encoding.
#[derive(Clone, Debug)]
pub struct Fp2Field<'a, F: SupportsQuadraticExtension> {
    base: &'a F,
    mone: Fp2Element<F>,
}

impl<'a, F: SupportsQuadraticExtension> Fp2Field<'a, F> {
    /// Constructs the non-serializable quadratic extension of `base`.
    pub fn new(base: &'a F) -> Self {
        let mone = Fp2Element {
            re: base.mone(),
            im: base.zero(),
        };

        Self { base, mone }
    }

    pub fn base_field(&self) -> &F {
        self.base
    }

    pub fn i(&self) -> Fp2Element<F> {
        Fp2Element {
            re: self.base.zero(),
            im: self.base.one(),
        }
    }
}

impl<F: SupportsQuadraticExtension> BareField for Fp2Field<'_, F> {
    type E = Fp2Element<F>;
}

impl<F: SupportsQuadraticExtension> crate::core::algebra::AlgebraicField for Fp2Field<'_, F> {
    fn zero(&self) -> Self::E {
        Fp2Element {
            re: self.base.zero(),
            im: self.base.zero(),
        }
    }

    fn one(&self) -> Self::E {
        Fp2Element {
            re: self.base.one(),
            im: self.base.zero(),
        }
    }

    fn add(&self, e1: &mut Self::E, e2: &Self::E) {
        self.base.add(&mut e1.re, &e2.re);
        self.base.add(&mut e1.im, &e2.im);
    }

    fn sub(&self, e1: &mut Self::E, e2: &Self::E) {
        self.base.sub(&mut e1.re, &e2.re);
        self.base.sub(&mut e1.im, &e2.im);
    }

    fn mul(&self, e1: &mut Self::E, e2: &Self::E) {
        let mut a01 = e1.re.clone();
        self.base.add(&mut a01, &e1.im);
        let mut b01 = e2.re.clone();
        self.base.add(&mut b01, &e2.im);

        let mut p1 = e1.im.clone();
        self.base.mul(&mut p1, &e2.im);

        self.base.mul(&mut e1.re, &e2.re);
        self.base.mul(&mut a01, &b01);
        self.base.sub(&mut a01, &e1.re);
        self.base.sub(&mut a01, &p1);

        self.base.sub(&mut e1.re, &p1);
        e1.im = a01;
    }

    fn invert(&self, e: &Self::E) -> Self::E {
        // (a + bi)^-1 = a/(a^2 + b^2) - b/(a^2 + b^2)i
        let a2 = self.base.mulf(&e.re, &e.re);
        let b2 = self.base.mulf(&e.im, &e.im);
        let denom = self.base.addf(&a2, &b2);
        let denom_inv = self.base.invert(&denom);

        Fp2Element {
            re: self.base.mulf(&e.re, &denom_inv),
            im: self.base.neg(&self.base.mulf(&e.im, &denom_inv)),
        }
    }

    fn mone(&self) -> Self::E {
        self.mone.clone()
    }
}

#[derive(PartialEq, Eq)]
pub struct Fp2Accum<F: SupportsQuadraticExtension>(pub Fp2Element<F>);

impl<F: SupportsQuadraticExtension> Clone for Fp2Accum<F> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<F: SupportsQuadraticExtension> std::fmt::Debug for Fp2Accum<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Fp2Accum").field("acc", &self.0).finish()
    }
}

impl<F: SupportsQuadraticExtension> RuntimeField for Fp2Field<'_, F> {
    type Accum = Fp2Accum<F>;

    fn zero_accum(&self) -> Self::Accum {
        Fp2Accum(self.zero())
    }

    fn mac(&self, acc: &mut Self::Accum, x: &Self::E, y: &Self::E) {
        let mut p = x.clone();
        self.mul(&mut p, y);
        self.add(&mut acc.0, &p);
    }

    fn accum_reduce(&self, acc: &Self::Accum) -> Self::E {
        acc.0.clone()
    }
}

impl<F: SupportsQuadraticExtension + SupportsU64Conversions> SupportsU64Conversions
    for Fp2Field<'_, F>
{
    fn u64_to_element(&self, n: u64) -> Self::E {
        Fp2Element {
            re: self.base.u64_to_element(n),
            im: self.base.zero(),
        }
    }
}
