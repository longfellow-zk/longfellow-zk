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

//! Exact arithmetic for offline certificate checks; never used by a proof role.
use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

pub(crate) fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    a = a.abs();
    b = b.abs();
    while !b.is_zero() {
        let r = a % &b;
        a = b;
        b = r;
    }
    a
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Q {
    pub n: BigInt,
    pub d: BigInt,
}
impl Q {
    pub(crate) fn new(mut n: BigInt, mut d: BigInt) -> Self {
        assert!(!d.is_zero(), "zero rational denominator");
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        let g = gcd(n.clone(), d.clone());
        Self {
            n: n / &g,
            d: d / g,
        }
    }
    pub(crate) fn int(n: impl Into<BigInt>) -> Self {
        Self {
            n: n.into(),
            d: BigInt::one(),
        }
    }
    #[cfg(test)]
    pub(crate) fn ratio(n: usize, d: usize) -> Self {
        Self::new(n.into(), d.into())
    }
    pub(crate) fn add(&self, b: &Self) -> Self {
        Self::new(&self.n * &b.d + &b.n * &self.d, &self.d * &b.d)
    }
    pub(crate) fn sub(&self, b: &Self) -> Self {
        self.add(&b.neg())
    }
    pub(crate) fn neg(&self) -> Self {
        Self {
            n: -&self.n,
            d: self.d.clone(),
        }
    }
    pub(crate) fn mul(&self, b: &Self) -> Self {
        let g = gcd(self.n.clone(), b.d.clone());
        let h = gcd(b.n.clone(), self.d.clone());
        Self::new((&self.n / &g) * (&b.n / &h), (&self.d / h) * (&b.d / g))
    }
    pub(crate) fn div(&self, b: &Self) -> Self {
        self.mul(&Self::new(b.d.clone(), b.n.clone()))
    }
    pub(crate) fn square(&self) -> Self {
        self.mul(self)
    }
    pub(crate) fn floor(&self) -> BigInt {
        let q = &self.n / &self.d;
        if self.n.is_negative() && !(&self.n % &self.d).is_zero() {
            q - 1
        } else {
            q
        }
    }
}
impl Ord for Q {
    fn cmp(&self, b: &Self) -> Ordering {
        (&self.n * &b.d).cmp(&(&b.n * &self.d))
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, b: &Self) -> Option<Ordering> {
        Some(self.cmp(b))
    }
}

pub(crate) fn choose(n: usize, r: usize) -> BigInt {
    if r > n {
        return BigInt::zero();
    }
    let mut v = BigInt::one();
    for i in 0..r.min(n - r) {
        v = v * (n - i) / (i + 1);
    }
    v
}
pub(crate) fn pow2(bits: u32) -> BigInt {
    BigInt::one() << bits
}
pub(crate) fn evaluate(coefficients: &[Q], x: usize) -> Q {
    coefficients
        .iter()
        .rev()
        .fold(Q::int(0), |value, coefficient| {
            coefficient.add(&Q::int(x).mul(&value))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rational_signs_and_floor() {
        assert_eq!(Q::new(2.into(), (-4).into()), Q::new((-1).into(), 2.into()));
        assert_eq!(Q::new((-3).into(), 2.into()).floor(), BigInt::from(-2));
        assert_eq!(Q::ratio(1, 3).add(&Q::ratio(1, 6)), Q::ratio(1, 2));
        assert_eq!(Q::ratio(7, 9).div(&Q::ratio(14, 3)), Q::ratio(1, 6));
    }
    #[test]
    fn binomial_matches_pascal() {
        let mut row = vec![BigInt::one()];
        for n in 0..40 {
            for (r, v) in row.iter().enumerate() {
                assert_eq!(&choose(n, r), v);
            }
            let mut next = vec![BigInt::one(); row.len() + 1];
            for r in 1..row.len() {
                next[r] = &row[r - 1] + &row[r];
            }
            row = next;
        }
        assert_eq!(choose(4, 5), BigInt::zero());
    }
}
