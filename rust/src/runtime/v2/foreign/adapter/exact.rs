// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exact mode for claims modulo the small prime q = 8380417 (ML-DSA).
//!
//! A claim of this mode lives in the sextic extension F_q^6, and every term's
//! value is a base-field integer held as a bit group. Coordinate `t` of the
//! claim is therefore an independent claim modulo q, so one claim is six
//! claims that share their bit groups.
//!
//! Every claim sum stays below 2^126 even for a dishonest prover, so exponent
//! sums never wrap modulo 2^128 - 1 and no conversion challenge is needed: a
//! tree checks the exact integer relation `S - C = q * k`. Three claims are
//! radix-packed into each of two trees. Each claim's quotient is a `Word<N>`,
//! so `N` must cover half the number of bits.
use super::{AdapterMode, Leaf, TreeInstance, TreeShape};
use crate::{
    core::{
        algebra::{fp24::Q, AlgebraicField, SupportsU128Conversions},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{
            fp24_ext6::{RuntimeElement, RuntimeFp24Ext6},
            gf2_128::{Gf2_128, Gf2_128Field},
        },
        v2::{
            foreign::{
                reserved::{BitGroup, ReservedSuffix},
                word::{MaskedWord, Otp},
            },
            proto::composed::AdapterMessage,
            transcript::{Bound, Header},
            zk::{
                storage::{Group, ModularClaim},
                VirtualInputs,
            },
        },
    },
    util::ceil_log2,
};

/// Base-field claims per extension claim: the six coordinates of F_q^6.
pub(crate) const CLAIMS: usize = 6;
/// Prime divisors of 2^128 - 1, the order of GF(2^128)^*.
pub(crate) const ORDER_FACTORS: [u128; 9] =
    [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721];

pub(crate) fn pow<F: AlgebraicField>(f: &F, mut base: F::E, mut exponent: u128) -> F::E {
    let mut out = f.one();
    while exponent != 0 {
        if exponent & 1 != 0 {
            f.mul(&mut out, &base);
        }
        base = f.mulf(&base, &base);
        exponent >>= 1;
    }
    out
}

/// Check the exact multiplicative order, including all prime divisors of 2^128-1.
/// The public tables are explicitly owned by each adapter instance.
pub(crate) fn generator<F: AlgebraicField + SupportsU128Conversions>(f: &F) -> F::E {
    assert_eq!(ORDER_FACTORS.iter().product::<u128>(), u128::MAX);
    for candidate in 2..256 {
        let g = f.u128_to_element(candidate);
        if ORDER_FACTORS
            .iter()
            .all(|q| pow(f, g.clone(), u128::MAX / q) != f.one())
        {
            return g;
        }
    }
    panic!("no primitive binary-field generator found")
}

fn signed_pow<F: AlgebraicField>(f: &F, g: &F::E, exponent: i128) -> F::E {
    let magnitude = exponent.unsigned_abs();
    let reduced_exponent = if exponent < 0 {
        u128::MAX - magnitude
    } else {
        magnitude
    };
    pow(f, g.clone(), reduced_exponent)
}

/// An exact-mode adapter instance whose six quotients are `Word<N>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactPlan<const N: usize> {
    widths: Vec<usize>,
    bits: usize,
    radix_bits: usize,
}
impl<const N: usize> ExactPlan<N> {
    pub(crate) const TREES: usize = 2;
    /// `widths` are the bit-group widths shared by all six claims.
    pub(crate) fn new(widths: Vec<usize>) -> Result<Self, String> {
        if widths.is_empty() || widths.iter().any(|&w| !(1..=23).contains(&w)) {
            return Err("exact adapter widths".into());
        }
        let bits = widths
            .iter()
            .try_fold(0usize, |total, &width| total.checked_add(width))
            .ok_or("exact adapter bit count overflow")?;
        // Every centered bit coefficient has magnitude <=(q-1)/2. After
        // adding the negative-coefficient offset, either choice of each bit
        // contributes in [0,(q-1)/2]. Hence the nonnegative quotient is strictly
        // below bits/2, independent of how bits are grouped into native words.
        let needed = ceil_log2(bits.div_ceil(2));
        // Each shifted sum is <bits*q/2; any allowed quotient RHS is <q*2^N < B.
        // Both packed sides are < B^3 <= 2^126 < 2^128-1, even dishonestly.
        if N == 0 || needed > N || N > 19 {
            return Err("exact adapter quotient width does not cover the claims".into());
        }
        Ok(Self {
            widths,
            bits,
            radix_bits: N + 23,
        })
    }
    pub(crate) fn shape(&self) -> TreeShape {
        TreeShape {
            trees: Self::TREES,
            leaves: self.bits + 3 * N,
        }
    }
    fn pack(&self, coordinates: [i128; 3]) -> i128 {
        coordinates[0]
            + (coordinates[1] << self.radix_bits)
            + (coordinates[2] << (2 * self.radix_bits))
    }
    /// Power weighing quotient bit `s` of claim `t`: g^(-q 2^(radix*(t%3)+s)).
    fn quotient_powers<F: AlgebraicField + SupportsU128Conversions>(&self, f: &F) -> Vec<F::E> {
        let g = generator(f);
        (0..CLAIMS)
            .flat_map(|t| {
                (0..N)
                    .map(|s| {
                        let exponent = -i128::from(Q) * (1i128 << ((t % 3) * self.radix_bits + s));
                        signed_pow(f, &g, exponent)
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub(crate) fn encode<F: AlgebraicField + SupportsU128Conversions>(
        &self,
        f: &F,
        claims: &ExactClaims,
    ) -> ExactEncoded<F::E> {
        assert_eq!(claims.weights.len(), self.widths.len());
        assert!(claims.targets.iter().all(|&a| a < Q));
        let g = generator(f);
        // Three-byte signed exponent tables for the three radix positions.
        let tables: Vec<_> = (0..3)
            .map(|t| {
                [1i128, -1]
                    .into_iter()
                    .map(|sign| {
                        (0..3)
                            .map(|byte| {
                                let base = signed_pow(
                                    f,
                                    &g,
                                    sign * (1i128 << (t * self.radix_bits + 8 * byte)),
                                );
                                let mut value = f.one();
                                (0..256)
                                    .map(|_| {
                                        let out = value.clone();
                                        f.mul(&mut value, &base);
                                        out
                                    })
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect();
        let small_power = |values: [i32; 3]| {
            let mut out = f.one();
            for (t, value) in values.into_iter().enumerate() {
                let magnitude = value.unsigned_abs();
                for byte in 0..3 {
                    f.mul(
                        &mut out,
                        &tables[t][usize::from(value < 0)][byte]
                            [((magnitude >> (8 * byte)) & 255) as usize],
                    );
                }
            }
            out
        };
        let corrections: Vec<_> = (0..27)
            .map(|code| {
                let eps = [code % 3 - 1, (code / 3) % 3 - 1, code / 9 - 1];
                signed_pow(f, &g, -i128::from(Q) * self.pack(eps.map(i128::from)))
            })
            .collect();
        #[cfg(any(test, feature = "prover"))]
        let mut centered = Vec::with_capacity(self.bits);
        let mut offsets = [0i128; CLAIMS];
        let mut coefficients = [Vec::with_capacity(self.bits), Vec::with_capacity(self.bits)];
        for (&width, weights) in self.widths.iter().zip(&claims.weights) {
            assert!(weights.iter().all(|&a| a < Q));
            let center = |a: u32| {
                if a > Q / 2 {
                    a as i32 - Q as i32
                } else {
                    a as i32
                }
            };
            let mut a = weights.map(center);
            let mut powers = [
                small_power([a[0], a[1], a[2]]),
                small_power([a[3], a[4], a[5]]),
            ];
            for bit in 0..width {
                #[cfg(any(test, feature = "prover"))]
                centered.push(a);
                for t in 0..CLAIMS {
                    offsets[t] += i128::from((-a[t]).max(0));
                }
                for (tree_coefficients, power) in coefficients.iter_mut().zip(&powers) {
                    tree_coefficients.push(f.subf(power, &f.one()));
                }
                if bit + 1 == width {
                    break;
                }
                let next = a.map(|x| center((i64::from(2 * x)).rem_euclid(i64::from(Q)) as u32));
                let eps: [i32; CLAIMS] = std::array::from_fn(|t| (2 * a[t] - next[t]) / Q as i32);
                for (tree, power) in powers.iter_mut().enumerate() {
                    let t = 3 * tree;
                    let code = eps[t] + 1 + 3 * (eps[t + 1] + 1) + 9 * (eps[t + 2] + 1);
                    *power = f.mulf(&f.mulf(power, power), &corrections[code as usize]);
                }
                a = next;
            }
        }
        let residues: [i128; CLAIMS] = std::array::from_fn(|t| {
            (i128::from(claims.targets[t]) + offsets[t]).rem_euclid(i128::from(Q))
        });
        let targets = std::array::from_fn(|tree| {
            signed_pow(
                f,
                &g,
                self.pack(std::array::from_fn(|i| {
                    residues[3 * tree + i] - offsets[3 * tree + i]
                })),
            )
        });
        ExactEncoded {
            coefficients,
            targets,
            #[cfg(any(test, feature = "prover"))]
            centered,
            #[cfg(any(test, feature = "prover"))]
            offsets,
            #[cfg(any(test, feature = "prover"))]
            residues,
        }
    }
}

/// Six claims modulo q over the same bit groups, one weight per group and claim.
pub(crate) struct ExactClaims {
    pub weights: Vec<[u32; CLAIMS]>,
    pub targets: [u32; CLAIMS],
}
impl ExactClaims {
    /// The six coordinate claims of one claim over F_q^6.
    pub(crate) fn from_claim(claim: &ModularClaim<RuntimeElement>) -> Self {
        Self {
            weights: claim.terms.iter().map(|(_, w)| *w.coefficients()).collect(),
            targets: *claim.target.coefficients(),
        }
    }
}
/// Leaf coefficients `g^A - 1` and targets of both trees; the centered
/// coefficients and offsets let the prover compute honest quotients.
pub(crate) struct ExactEncoded<E> {
    pub coefficients: [Vec<E>; 2],
    pub targets: [E; 2],
    #[cfg(any(test, feature = "prover"))]
    centered: Vec<[i32; CLAIMS]>,
    #[cfg(any(test, feature = "prover"))]
    offsets: [i128; CLAIMS],
    #[cfg(any(test, feature = "prover"))]
    residues: [i128; CLAIMS],
}
#[cfg(any(test, feature = "prover"))]
impl<E> ExactEncoded<E> {
    /// Honest quotients from the committed bits, in group order.
    pub(crate) fn quotients<const N: usize>(
        &self,
        plan: &ExactPlan<N>,
        bits: &[bool],
    ) -> Result<[Word<N>; CLAIMS], String> {
        if bits.len() != plan.bits || self.centered.len() != plan.bits {
            return Err("adapter bit count".into());
        }
        let mut sums = self.offsets;
        for (bit, a) in bits.iter().zip(&self.centered) {
            if *bit {
                for t in 0..CLAIMS {
                    sums[t] += i128::from(a[t]);
                }
            }
        }
        let mut out = [Word::new(0)?; CLAIMS];
        for t in 0..CLAIMS {
            let delta = sums[t] - self.residues[t];
            if delta < 0 || delta % i128::from(Q) != 0 || delta / i128::from(Q) >= 1i128 << N {
                return Err(format!("adapter unsatisfied prime-field claim {t}"));
            }
            out[t] = Word::new((delta / i128::from(Q)) as u64)?;
        }
        Ok(out)
    }
}
impl ExactEncoded<Gf2_128> {
    /// Assemble both trees: data leaves over `groups`, then three claims'
    /// quotient leaves, each selected by its masked word over its pad.
    pub(crate) fn trees<const N: usize>(
        &self,
        plan: &ExactPlan<N>,
        groups: &[Group],
        otp: &[BitGroup<N>; CLAIMS],
        masked: &[MaskedWord<N>; CLAIMS],
        f: &Gf2_128Field,
    ) -> Result<Vec<TreeInstance>, String> {
        if groups.len() != plan.widths.len()
            || groups
                .iter()
                .zip(&plan.widths)
                .any(|(g, &w)| g.width() != w)
        {
            return Err("exact adapter groups".into());
        }
        let powers = plan.quotient_powers(f);
        Ok((0..2)
            .map(|tree| {
                let sources = groups.iter().flat_map(|g| (0..g.width()).map(|r| g.bit(r)));
                let mut leaves: Vec<_> = sources
                    .zip(&self.coefficients[tree])
                    .map(|(source, c)| Leaf::data(source, *c, f))
                    .collect();
                for t in 3 * tree..3 * tree + 3 {
                    let pad = otp[t].group();
                    leaves.extend((0..N).map(|s| {
                        Leaf::quotient(pad.bit(s), powers[t * N + s], masked[t].bit(s), f)
                    }));
                }
                TreeInstance {
                    leaves,
                    target: self.targets[tree],
                }
            })
            .collect())
    }
}

mod transcript;
use transcript::absorb_masked;

impl<const N: usize> AdapterMessage for [MaskedWord<N>; CLAIMS] {
    const BYTES: usize = CLAIMS * N.div_ceil(8);
}
#[cfg(any(test, feature = "prover"))]
impl<const N: usize> crate::runtime::v2::proto::composed::WriteAdapterMessage
    for [MaskedWord<N>; CLAIMS]
{
    fn write(&self, out: &mut Vec<u8>) {
        for m in self {
            m.write(out);
        }
    }
}
#[cfg(any(test, feature = "verifier"))]
impl<const N: usize> crate::runtime::v2::proto::composed::ReadAdapterMessage
    for [MaskedWord<N>; CLAIMS]
{
    fn read(b: &mut &[u8]) -> Result<Self, String> {
        let mut out = [MaskedWord::read(b)?; CLAIMS];
        for m in &mut out[1..] {
            *m = MaskedWord::read(b)?;
        }
        Ok(out)
    }
}

/// The exact mode as an adapter mode: two trees, each with three `Word<N>`
/// quotients published as `MaskedWord<N>` over committed `Otp<N>` pads.
///
/// Its claims carry no split mask: they are either projections of public
/// data or the whole claim of a pure-foreign participant, so `MASK_BITS` is
/// zero and the mixed-storage composition driver cannot use this mode.
pub(crate) struct ExactMode<const N: usize> {
    plan: ExactPlan<N>,
    otp: [BitGroup<N>; CLAIMS],
    shape: TreeShape,
    fragment: Circuit<Gf2_128Field>,
}
impl<const N: usize> ExactMode<N> {
    fn check(&self, claim: &ModularClaim<RuntimeElement>) -> Result<Vec<Group>, String> {
        if claim.terms.len() != self.plan.widths.len()
            || claim
                .terms
                .iter()
                .zip(&self.plan.widths)
                .any(|((g, _), &w)| g.width() != w)
        {
            return Err("exact adapter claim shape".into());
        }
        Ok(claim.terms.iter().map(|(g, _)| *g).collect())
    }
}
impl<const N: usize> AdapterMode<RuntimeFp24Ext6> for ExactMode<N> {
    const MASK_BITS: usize = 0;
    // Composition's generic split requires every bit pattern to be canonical:
    // 2^22 < q < 2^23. ExactPlan separately accepts 23-bit groups for the
    // custom pure ML-DSA driver, which does not use Composition (MASK_BITS=0)
    // and supplies canonical coordinate values directly.
    const MAX_VALUE_BITS: usize = 22;
    type Pads = [Otp<N>; CLAIMS];
    type Message = [MaskedWord<N>; CLAIMS];
    fn new(
        widths: Vec<usize>,
        npublic: usize,
        suffix: &mut ReservedSuffix,
    ) -> Result<Self, String> {
        let plan = ExactPlan::new(widths)?;
        let first = suffix.word::<N>()?;
        let mut otp = [first; CLAIMS];
        for group in &mut otp[1..] {
            *group = suffix.word::<N>()?;
        }
        let shape = plan.shape();
        let fragment = super::fragment(npublic, suffix.end(), shape)?;
        Ok(Self {
            plan,
            otp,
            shape,
            fragment,
        })
    }
    fn fragment(&self) -> &Circuit<Gf2_128Field> {
        &self.fragment
    }
    fn virtual_inputs(&self) -> usize {
        self.shape
            .virtual_inputs()
            .expect("validated exact adapter shape")
    }
    fn write_layout(&self, h: &mut Header<'_>) {
        transcript::write_layout::<N>(h, self.shape, self.otp.map(|p| p.group()));
    }
    #[cfg(any(test, feature = "prover"))]
    fn sample_pads(&self, rng: &mut impl PrivateRandom) -> Self::Pads {
        std::array::from_fn(|_| Otp::sample(rng))
    }
    #[cfg(any(test, feature = "prover"))]
    fn write_pads(
        &self,
        pads: &Self::Pads,
        reserved: &mut ReservedWitness<'_>,
    ) -> Result<(), String> {
        for (group, pad) in self.otp.iter().zip(pads) {
            reserved.set(group.group(), pad.bits())?;
        }
        Ok(())
    }
    /// `values` are the terms' base-field integers, each within its group.
    #[cfg(any(test, feature = "prover"))]
    fn prove(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<RuntimeElement>,
        values: &[RuntimeElement],
        pads: Self::Pads,
        _: &RuntimeFp24Ext6,
        f: &Gf2_128Field,
    ) -> Result<(Self::Message, VirtualInputs<Gf2_128>), String> {
        let mode = t.part();
        let groups = mode.check(claim)?;
        if values.len() != groups.len() {
            return Err("exact adapter value count".into());
        }
        let mut bits = Vec::with_capacity(mode.plan.bits);
        for (g, v) in groups.iter().zip(values) {
            let c = v.coefficients();
            if c[1..].iter().any(|&x| x != 0) || u64::from(c[0]) >> g.width() != 0 {
                return Err("exact adapter value exceeds its group".into());
            }
            bits.extend((0..g.width()).map(|r| c[0] >> r & 1 != 0));
        }
        let encoded = mode.plan.encode(f, &ExactClaims::from_claim(claim));
        let quotients = encoded.quotients(&mode.plan, &bits)?;
        let mut words = quotients.into_iter().zip(pads);
        let masked = std::array::from_fn(|_| {
            let (quotient, pad) = words.next().expect("exact adapter pad count");
            MaskedWord::mask(quotient, pad)
        });
        absorb_masked(&mut t.transcript(), &masked);
        let trees = encoded.trees(&mode.plan, &groups, &mode.otp, &masked, f)?;
        Ok((masked, super::virtual_inputs(mode.shape, trees, f)?))
    }
    #[cfg(any(test, feature = "verifier"))]
    fn verify(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<RuntimeElement>,
        masked: &Self::Message,
        _: &RuntimeFp24Ext6,
        f: &Gf2_128Field,
    ) -> Result<VirtualInputs<Gf2_128>, String> {
        let mode = t.part();
        let groups = mode.check(claim)?;
        let encoded = mode.plan.encode(f, &ExactClaims::from_claim(claim));
        absorb_masked(&mut t.transcript(), masked);
        let trees = encoded.trees(&mode.plan, &groups, &mode.otp, masked, f)?;
        super::virtual_inputs(mode.shape, trees, f)
    }
}

#[cfg(test)]
mod tests;

#[cfg(any(test, feature = "prover"))]
use crate::runtime::{
    random::PrivateRandom,
    v2::foreign::{reserved::ReservedWitness, word::Word},
};
