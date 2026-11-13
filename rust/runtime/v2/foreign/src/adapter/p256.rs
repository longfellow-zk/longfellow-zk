// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Wrapping mode for claims modulo the P-256 coordinate prime p.
//!
//! Since p exceeds the group order M = 2^128 - 1 of GF(2^128)^*, exponent sums
//! wrap modulo M and a false claim can survive a single rescaling with
//! probability about 2^-117. Two independent full-field conversion challenges
//! give two trees. Each tree checks `g^(S - C) = X^k`, where `g^(-p) = X` and
//! the honest quotient `k = (S - C) / p` is below `2^Q`.
use super::{
    integer::{self, Int256},
    Leaf, TreeInstance, TreeShape,
};
#[cfg(any(test, feature = "prover"))]
use crate::runtime::v2::foreign::word::Word;
use crate::{
    core::algebra::{AlgebraicField, SerializableField, SupportsU128Conversions},
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            p256::{P256Element, P256Field},
        },
        v2::{
            foreign::word::MaskedWord,
            zk::storage::{BitGroup, ModularClaim},
        },
    },
};

/// P-256 coordinate modulus, little-endian limbs. The scalar order differs.
pub(crate) const MODULUS: [u64; 4] = [
    0xffffffffffffffff,
    0x00000000ffffffff,
    0,
    0xffffffff00000001,
];
const ORDER_FACTORS: [u128; 9] = [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721];

fn pow<F: AlgebraicField>(f: &F, mut b: F::E, mut n: u128) -> F::E {
    let mut x = f.one();
    while n != 0 {
        if n & 1 != 0 {
            f.mul(&mut x, &b);
        }
        b = f.mulf(&b, &b);
        n >>= 1;
    }
    x
}

pub(crate) fn to_int(p: &P256Field, value: &P256Element) -> Int256 {
    let bytes = p.to_bytes(value);
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

/// A P-256 adapter instance whose quotients are `Word<Q>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct P256Plan<const Q: usize> {
    widths: Vec<usize>,
    bits: usize,
}
impl<const Q: usize> P256Plan<Q> {
    pub const TREES: usize = 2;
    /// `widths` are the claim's bit-group widths, in term order. The quotient
    /// of each tree is below the number of bits, which must fit in `Q` bits.
    pub fn new(widths: Vec<usize>) -> Result<Self, String> {
        let bits = widths
            .iter()
            .try_fold(0usize, |n, &w| {
                if !(1..=256).contains(&w) {
                    return None;
                }
                n.checked_add(w)
            })
            .ok_or("P256 adapter widths")?;
        if bits < 2 || Q >= usize::BITS as usize || bits > 1usize << Q {
            return Err("P256 adapter quotient width does not cover the claim".into());
        }
        Ok(Self { widths, bits })
    }
    pub fn shape(&self) -> TreeShape {
        TreeShape {
            trees: Self::TREES,
            leaves: self.bits + Q,
        }
    }
    fn quotient_powers(f: &Gf2_128Field) -> Vec<Gf2_128> {
        // g^(-p) = X, so X^(2^j) weighs quotient bit j.
        let mut x = f.u128_to_element(2);
        (0..Q)
            .map(|_| {
                let out = x;
                x = f.mulf(&x, &x);
                out
            })
            .collect()
    }

    /// Leaf coefficients, targets and (with `values`) the honest quotients.
    /// Both challenges must be independent, nonzero, uniform full prime-field
    /// samples drawn after the claim is fixed.
    // Verifier-only builds omit the prover's quotient accumulation, which is
    // the only user of `values` and of some loop indices.
    #[cfg_attr(not(any(test, feature = "prover")), allow(unused_variables))]
    pub fn encode(
        &self,
        claim: &ModularClaim<P256Element>,
        alpha: &[P256Element; 2],
        values: Option<&[P256Element]>,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<P256Encoded<Q>, String> {
        if claim.terms.len() != self.widths.len()
            || claim
                .terms
                .iter()
                .zip(&self.widths)
                .any(|((g, _), &w)| g.width != w)
            || alpha.iter().any(|a| p.is_zero(a))
            || values.is_some_and(|v| v.len() != claim.terms.len())
        {
            return Err("P256 adapter claim shape or zero challenge".into());
        }
        let x = f.u128_to_element(2);
        assert!(ORDER_FACTORS
            .iter()
            .all(|q| pow(f, x, u128::MAX / q) != f.one()));
        let g = pow(f, x, u128::MAX - (1u128 << 64));
        // Owned 16-byte-position fixed-base table, about 64 KiB.
        let mut base = g;
        let tables: Vec<Vec<Gf2_128>> = (0..16)
            .map(|_| {
                let mut value = f.one();
                let table = (0..256)
                    .map(|_| {
                        let out = value;
                        f.mul(&mut value, &base);
                        out
                    })
                    .collect();
                for _ in 0..8 {
                    base = f.mulf(&base, &base);
                }
                table
            })
            .collect();
        let exponent = |word: Int256| {
            let e = integer::reduce_exponent(word);
            (0..16).fold(f.one(), |mut out, i| {
                f.mul(&mut out, &tables[i][((e >> (8 * i)) & 255) as usize]);
                out
            })
        };
        let targets = alpha
            .each_ref()
            .map(|a| to_int(p, &p.mulf(a, &claim.target)));
        let mut coefficients = [Vec::with_capacity(self.bits), Vec::with_capacity(self.bits)];
        // The honest quotients are prover-only; verifiers pass no values, and
        // verifier-only builds compile none of this accumulation.
        #[cfg(any(test, feature = "prover"))]
        let mut sums = [[0u64; 5]; 2];
        for (tree, scaling) in alpha.iter().enumerate() {
            for (j, (group, c)) in claim.terms.iter().enumerate() {
                let mut a = to_int(p, &p.mulf(scaling, c));
                let mut power = exponent(a);
                #[cfg(any(test, feature = "prover"))]
                let value = values.map(|v| to_int(p, &v[j]));
                #[cfg(any(test, feature = "prover"))]
                if value.is_some_and(|v| (group.width..256).any(|r| integer::bit(&v, r))) {
                    return Err("P256 adapter value exceeds its group".into());
                }
                for r in 0..group.width {
                    coefficients[tree].push(f.subf(&power, &f.one()));
                    #[cfg(any(test, feature = "prover"))]
                    if let Some(v) = value {
                        if integer::bit(&v, r) {
                            integer::add_word(&mut sums[tree], &a);
                        }
                    }
                    let correction = integer::double(&mut a);
                    power = f.mulf(&power, &power);
                    if correction {
                        f.mul(&mut power, &x);
                    }
                }
            }
        }
        #[cfg(any(test, feature = "prover"))]
        let quotients = if values.is_some() {
            let mut out = [Word::new(0)?; 2];
            for (tree, c) in targets.into_iter().enumerate() {
                if !integer::subtract_word(&mut sums[tree], &c) {
                    return Err("P256 adapter negative quotient".into());
                }
                let (q, rem) = integer::divide(&sums[tree]);
                if rem != [0; 4] || q[1..].iter().any(|&x| x != 0) {
                    return Err("P256 adapter unsatisfied claim".into());
                }
                out[tree] = Word::new(q[0])?;
            }
            Some(out)
        } else {
            None
        };
        Ok(P256Encoded {
            coefficients,
            targets: targets.map(exponent),
            #[cfg(any(test, feature = "prover"))]
            quotients,
        })
    }
}

/// Encoded claim: per-tree data-leaf coefficients `g^A - 1`, root targets and,
/// for the prover only, the honest quotients.
pub struct P256Encoded<const Q: usize> {
    coefficients: [Vec<Gf2_128>; 2],
    targets: [Gf2_128; 2],
    /// Honest quotients, computed only by provers.
    #[cfg(any(test, feature = "prover"))]
    pub quotients: Option<[Word<Q>; 2]>,
}
impl<const Q: usize> P256Encoded<Q> {
    /// Assemble both trees from the claim's bit groups, the committed pads and
    /// the published masked quotients.
    pub fn trees(
        &self,
        claim: &ModularClaim<P256Element>,
        otp: &[BitGroup<Q>; 2],
        masked: &[MaskedWord<Q>; 2],
        f: &Gf2_128Field,
    ) -> Vec<TreeInstance> {
        let powers = P256Plan::<Q>::quotient_powers(f);
        (0..2)
            .map(|tree| {
                let sources = claim
                    .terms
                    .iter()
                    .flat_map(|(g, _)| (0..g.width).map(|r| g.bit(r)));
                let mut leaves: Vec<_> = sources
                    .zip(&self.coefficients[tree])
                    .map(|(source, c)| Leaf::data(source, *c, f))
                    .collect();
                let pad = otp[tree].group();
                leaves.extend(
                    (0..Q).map(|j| Leaf::quotient(pad.bit(j), powers[j], masked[tree].bit(j), f)),
                );
                TreeInstance {
                    leaves,
                    target: self.targets[tree],
                }
            })
            .collect()
    }
}

pub use super::transcript::{absorb_masked, conversion};
