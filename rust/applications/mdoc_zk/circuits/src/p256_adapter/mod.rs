// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Convert P256 coordinate-field claims into two binary-field product equations.
//! Both fields use masked sumcheck; the ECDSA scalar order is not used here.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod integer;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use integer::Word;
/// P256 coordinate modulus, little-endian limbs. The scalar order differs.
pub(crate) const MODULUS: [u64; 4] = [
    0xffffffffffffffff,
    0x00000000ffffffff,
    0,
    0xffffffff00000001,
];

#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::core::algebra::SerializableField;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::core::algebra::{AlgebraicField, SupportsU128Conversions};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::algebra::{
    gf2_128::{Gf2_128, Gf2_128Field},
    p256::{P256Element, P256Field},
};

const MAX_BITS: usize = 1 << 24;

#[derive(Clone, Debug)]
pub(crate) struct Plan {
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub widths: Vec<usize>,
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub bits: usize,
    pub quotient_bits: usize,
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub powers: usize,
}
impl Plan {
    pub(crate) fn new(widths: Vec<usize>) -> Result<Self, String> {
        let bits = widths
            .iter()
            .try_fold(0usize, |n, &w| {
                if !(1..=256).contains(&w) {
                    return None;
                }
                n.checked_add(w)
            })
            .ok_or("P256 adapter widths")?;
        if !(2..=MAX_BITS).contains(&bits) {
            return Err("P256 adapter bit capacity".into());
        }
        Ok(Self {
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            widths,
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            bits,
            quotient_bits: bits.next_power_of_two().ilog2() as usize,
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            powers: 2 * bits,
        })
    }
    pub(crate) fn advice_bits(&self) -> usize {
        2 * self.quotient_bits
    }
    pub(crate) fn advice_bytes(&self) -> usize {
        self.advice_bits().div_ceil(8)
    }
    /// Advice has an exact byte length and zeroes above its final quotient bit.
    pub(crate) fn validate_advice(&self, bytes: &[u8]) -> Result<(), String> {
        let used = self.advice_bits() % 8;
        if bytes.len() != self.advice_bytes()
            || (used != 0 && bytes.last().is_some_and(|&b| b >> used != 0))
        {
            return Err("noncanonical adapter advice".into());
        }
        Ok(())
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn public_count(&self) -> usize {
        2 * self.bits + self.advice_bits() + 2
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn quotient_coefficients<F: AlgebraicField + SupportsU128Conversions>(
        &self,
        f: &F,
    ) -> Vec<F::E> {
        // g^(-p) = X. These are the same for both quotient trees.
        let mut x = f.u128_to_element(2);
        (0..self.quotient_bits)
            .map(|_| {
                let coefficient = f.subf(&x, &f.one());
                x = f.mulf(&x, &x);
                coefficient
            })
            .collect()
    }

    /// Generate two independent power sequences and the honest quotients.
    /// Both challenges must be independent, nonzero, uniform FULL prime-field
    /// samples after the root and complete prime claim are fixed.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn encode(
        &self,
        weights: &[P256Element],
        target: &P256Element,
        alpha: &[P256Element; 2],
        values: Option<&[P256Element]>,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<Encoded, String> {
        if weights.len() != self.widths.len()
            || alpha.iter().any(|a| p.is_zero(a))
            || values.is_some_and(|v| v.len() != weights.len())
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
        let exponent = |word: Word| {
            let e = integer::reduce_exponent(word);
            (0..16).fold(f.one(), |mut out, i| {
                f.mul(&mut out, &tables[i][((e >> (8 * i)) & 255) as usize]);
                out
            })
        };
        let targets = alpha.each_ref().map(|a| to_word(p, &p.mulf(a, target)));
        let mut coefficients = Vec::with_capacity(self.powers);
        let mut sums = [[0u64; 5]; 2];
        // Tree-major layout keeps each public coefficient column contiguous.
        for (tree, scaling) in alpha.iter().enumerate() {
            for (j, (&width, a)) in self.widths.iter().zip(weights).enumerate() {
                let mut a = to_word(p, &p.mulf(scaling, a));
                let mut power = exponent(a);
                let value = values.map(|v| to_word(p, &v[j]));
                if value.is_some_and(|v| (width..256).any(|r| integer::bit(&v, r))) {
                    return Err("P256 adapter value exceeds width".into());
                }
                for r in 0..width {
                    coefficients.push(f.subf(&power, &f.one()));
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
        let quotients = if values.is_some() {
            let mut out = [0u32; 2];
            for (tree, c) in targets.into_iter().enumerate() {
                if !integer::subtract_word(&mut sums[tree], &c) {
                    return Err("P256 adapter negative quotient".into());
                }
                let (q, rem) = integer::divide(&sums[tree]);
                if rem != [0; 4]
                    || q[1..].iter().any(|&x| x != 0)
                    || q[0] >= (1u64 << self.quotient_bits)
                {
                    return Err("P256 adapter unsatisfied prime claim".into());
                }
                out[tree] = q[0] as u32;
            }
            Some(out)
        } else {
            None
        };
        Ok(Encoded {
            coefficients,
            targets: targets.map(exponent),
            quotients,
        })
    }
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) struct Encoded {
    pub coefficients: Vec<Gf2_128>,
    pub targets: [Gf2_128; 2],
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    pub quotients: Option<[u32; 2]>,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) fn to_word(p: &P256Field, value: &P256Element) -> Word {
    let bytes = p.to_bytes(value);
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
const ORDER_FACTORS: [u128; 9] = [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721];
#[cfg(any(test, feature = "prover", feature = "verifier"))]
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

#[cfg(test)]
#[path = "../../tests/p256_adapter.rs"]
mod tests;
pub(crate) const SHARED_BITS: usize = 768;
pub(crate) const MASK_BITS: usize = 256;
/// The mask and both quotient OTPs occupy an unused suffix of c_hash inputs.
#[cfg(any(test, feature = "compiler"))]
pub(crate) const AUXILIARY_BITS: usize =
    MASK_BITS + 2 * (SHARED_BITS + MASK_BITS).next_power_of_two().ilog2() as usize;
#[cfg(test)]
pub(crate) mod hash_inputs;
pub(crate) fn shared_plan() -> Plan {
    let mut widths = vec![1; SHARED_BITS];
    widths.push(MASK_BITS);
    Plan::new(widths).unwrap()
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) mod tree;
