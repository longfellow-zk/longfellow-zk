// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Wrapping mode for claims modulo the P-256 coordinate prime p.
//!
//! Since p exceeds the group order M = 2^128 - 1 of GF(2^128)^*, exponent sums
//! wrap modulo M and a false claim can survive a single rescaling with
//! probability about 2^-117. Two independent full-field conversion challenges
//! give two trees. Each tree checks `g^(S - C) * X^k = 1`, that is
//! `g^(S - C) = X^(-k)`, where `g^(-p) = X` and the honest quotient
//! `k = (S - C) / p` is below `2^Q`.
mod integer;
pub mod transcript;

use integer::Int256;
use transcript::Conversion;

use super::{Leaf, TreeInstance, TreeShape};
#[cfg(test)]
use crate::runtime::v2::transcript::cheat;
#[cfg(any(test, feature = "prover"))]
use crate::runtime::{random::PrivateRandom, v2::foreign::word::Word};
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField, SupportsU128Conversions},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            p256::{P256Element, P256Field},
        },
        v2::{
            foreign::word::MaskedWord,
            transcript::{Bound, Challenge, Header},
            zk::{
                storage::{BitGroup, ModularClaim, ReservedSuffix},
                VirtualInputs,
            },
        },
    },
};

/// g = X^(M - 2^64), so that g^(-p) = X, with M = 2^128 - 1 and p = 2^64 mod M.
const GENERATOR_EXPONENT: u128 = u128::MAX - (1u128 << 64);

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
///
/// Its encoder takes the conversion challenges as plain field elements and
/// is crate-private; applications reach it only through `P256Mode`, whose
/// rounds draw the challenges from the transcript:
///
/// ```compile_fail,E0624
/// use longfellow_zk::runtime::{
///     algebra::{
///         gf2_128::Gf2_128Field,
///         p256::{P256Element, P256Field},
///     },
///     v2::{foreign::adapter::p256::P256Plan, zk::storage::ModularClaim},
/// };
/// fn chosen(
///     plan: &P256Plan<10>,
///     claim: &ModularClaim<P256Element>,
///     alpha: &[P256Element; 2],
///     p: &P256Field,
///     f: &Gf2_128Field,
/// ) {
///     let _ = plan.encode(claim, alpha, None, p, f);
/// }
/// ```
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
    /// samples drawn after the claim is fixed. This checks only that they are
    /// nonzero, so it is crate-private: outside tests, only `P256Mode` calls
    /// it, with the transcript's `Challenge<Conversion>`.
    // Verifier-only builds omit the prover's quotient accumulation, which is
    // the only user of `values` and of some loop indices.
    #[cfg_attr(not(any(test, feature = "prover")), allow(unused_variables))]
    pub(crate) fn encode(
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
                .any(|((g, _), &w)| g.width() != w)
            || alpha.iter().any(|a| p.is_zero(a))
            || values.is_some_and(|v| v.len() != claim.terms.len())
        {
            return Err("P256 adapter claim shape or zero challenge".into());
        }
        // X is primitive (the unit test `adapter_base_is_primitive` checks it
        // on every arithmetic backend), so g, a power of X coprime to M, is.
        let x = f.u128_to_element(2);
        let g = pow(f, x, GENERATOR_EXPONENT);
        // Fixed-base table of g^(2^i) for each bit i of a reduced exponent:
        // 127 squarings and 2 KiB on the stack, shared by every exponent of
        // both conversion challenges in this proof operation.
        let mut powers = [g; 128];
        for i in 1..128 {
            powers[i] = f.mulf(&powers[i - 1], &powers[i - 1]);
        }
        let exponent = |word: Int256| {
            let mut e = integer::reduce_exponent(word);
            let mut out = f.one();
            while e != 0 {
                f.mul(&mut out, &powers[e.trailing_zeros() as usize]);
                e &= e - 1;
            }
            out
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
                let exceeds =
                    value.is_some_and(|v| (group.width()..256).any(|r| integer::bit(&v, r)));
                // A cheating test prover (`transcript::cheat`) goes on.
                #[cfg(test)]
                #[allow(clippy::shadow_reuse)]
                let exceeds = exceeds && !cheat::active();
                #[cfg(any(test, feature = "prover"))]
                if exceeds {
                    return Err("P256 adapter value exceeds its group".into());
                }
                for r in 0..group.width() {
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
                let nonnegative = integer::subtract_word(&mut sums[tree], &c);
                // A cheating test prover sends the low Q bits of whatever the
                // division gives.
                #[cfg(test)]
                if cheat::active() {
                    out[tree] = Word::new(integer::divide(&sums[tree]).0[0] & ((1 << Q) - 1))?;
                    continue;
                }
                if !nonnegative {
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
pub(crate) struct P256Encoded<const Q: usize> {
    coefficients: [Vec<Gf2_128>; 2],
    targets: [Gf2_128; 2],
    /// Honest quotients, computed only by provers.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) quotients: Option<[Word<Q>; 2]>,
}
impl<const Q: usize> P256Encoded<Q> {
    /// Assemble both trees from the claim's bit groups, the committed pads and
    /// the published masked quotients.
    pub(crate) fn trees(
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
                    .flat_map(|(g, _)| (0..g.width()).map(|r| g.bit(r)));
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

/// The P-256 wrapping mode as an adapter mode: two trees, each with a
/// `Word<Q>` quotient published as `MaskedWord<Q>` over a committed `Otp<Q>`.
///
/// The adapter's conversion pair and masked quotients enter the transcript
/// only through the mode: `draw_conversion` stamps the pair as the mode's
/// input challenge and `prove` and `verify` send the quotients. The raw
/// steps are not public:
///
/// ```compile_fail,E0432
/// use longfellow_zk::runtime::v2::foreign::adapter::p256::transcript::conversion;
/// ```
///
/// ```compile_fail,E0603
/// use longfellow_zk::runtime::v2::foreign::adapter::p256::transcript::send_quotients;
/// ```
pub struct P256Mode<const Q: usize> {
    plan: P256Plan<Q>,
    otp: [BitGroup<Q>; 2],
    shape: TreeShape,
    /// `shape.virtual_inputs()`, checked when the fragment was built.
    virtual_inputs: usize,
    fragment: Circuit<Gf2_128Field>,
}
impl<const Q: usize> super::AdapterMode<P256Field> for P256Mode<Q> {
    const MASK_BITS: usize = 256;
    type Pads = [crate::runtime::v2::foreign::word::Otp<Q>; 2];
    type Message = [MaskedWord<Q>; 2];
    type Conversion = Conversion;
    fn new(
        widths: Vec<usize>,
        npublic: usize,
        suffix: &mut ReservedSuffix,
    ) -> Result<Self, String> {
        let otp = [suffix.word::<Q>()?, suffix.word::<Q>()?];
        let plan = P256Plan::new(widths)?;
        let shape = plan.shape();
        let fragment = super::fragment(npublic, suffix.end(), shape)?;
        let virtual_inputs = shape.virtual_inputs().ok_or("adapter fragment width")?;
        Ok(Self {
            plan,
            otp,
            shape,
            virtual_inputs,
            fragment,
        })
    }
    fn fragment(&self) -> &Circuit<Gf2_128Field> {
        &self.fragment
    }
    fn virtual_inputs(&self) -> usize {
        self.virtual_inputs
    }
    fn write_layout(&self, h: &mut Header<'_>) {
        transcript::write_layout::<Q>(h, self.shape, self.otp.map(|g| g.group()));
    }
    #[cfg(any(test, feature = "prover"))]
    fn sample_pads(&self, rng: &mut impl PrivateRandom) -> Self::Pads {
        use crate::runtime::v2::foreign::word::Otp;
        [Otp::sample(rng), Otp::sample(rng)]
    }
    #[cfg(any(test, feature = "prover"))]
    fn write_pads(
        &self,
        pads: &Self::Pads,
        reserved: &mut crate::runtime::v2::zk::storage::ReservedWitness<'_>,
    ) -> Result<(), String> {
        for (group, pad) in self.otp.iter().zip(pads) {
            reserved.set(group.group(), pad.bits())?;
        }
        Ok(())
    }
    fn draw_conversion(t: &mut Bound<'_, Self>, p: &P256Field) -> Challenge<Conversion> {
        transcript::draw_conversion(t, p)
    }
    #[cfg(any(test, feature = "prover"))]
    fn prove(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<P256Element>,
        values: &[P256Element],
        pads: Self::Pads,
        conversion: Challenge<Conversion>,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<(Self::Message, VirtualInputs<Gf2_128>), String> {
        let mode = t.part();
        let Conversion(alpha) = t.accept(conversion).map_err(|e| e.to_string())?;
        let encoded = mode.plan.encode(claim, &alpha, Some(values), p, f)?;
        let k = encoded.quotients.ok_or("P256 adapter quotients")?;
        let [o0, o1] = pads;
        let masked = [MaskedWord::mask(k[0], o0), MaskedWord::mask(k[1], o1)];
        transcript::send_quotients(&mut t.transcript(), &masked);
        let leaves =
            super::virtual_inputs(mode.shape, encoded.trees(claim, &mode.otp, &masked, f), f)?;
        Ok((masked, leaves))
    }
    #[cfg(any(test, feature = "verifier"))]
    fn verify(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<P256Element>,
        masked: &Self::Message,
        conversion: Challenge<Conversion>,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<VirtualInputs<Gf2_128>, String> {
        let mode = t.part();
        let Conversion(alpha) = t.accept(conversion).map_err(|e| e.to_string())?;
        let encoded = mode.plan.encode(claim, &alpha, None, p, f)?;
        transcript::send_quotients(&mut t.transcript(), masked);
        super::virtual_inputs(mode.shape, encoded.trees(claim, &mode.otp, masked, f), f)
    }
}

#[cfg(test)]
mod tests;
