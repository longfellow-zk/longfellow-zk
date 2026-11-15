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
pub(crate) mod transcript;
use integer::Int256;
use transcript::{send_quotients, Conversion};

#[cfg(test)]
use super::TreeInstance;
use super::{
    super::reserved::{BitGroup, ReservedSuffix},
    Leaf, TreeShape,
};
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
            transcript::{Bound, Header},
            zk::{storage::ModularClaim, VirtualInput, VirtualInputs},
        },
    },
};

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
    let mut bytes = [0u8; 32];
    p.to_bytes_into(value, &mut bytes);
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

/// A P-256 adapter instance whose quotients are `Word<Q>`.
///
/// Its encoder takes the conversion challenges as plain field elements and
/// is crate-private; applications reach it only through `P256Mode`, whose
/// rounds draw the challenges from the transcript:
///
/// ```compile_fail,E0603
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
pub(crate) struct P256Plan<const Q: usize> {
    widths: Vec<usize>,
    bits: usize,
}
impl<const Q: usize> P256Plan<Q> {
    pub(crate) const TREES: usize = 2;
    /// `widths` are the claim's bit-group widths, in term order. The quotient
    /// of each tree is below the number of bits, which must fit in `Q` bits.
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
        if bits < 2 || Q >= usize::BITS as usize || bits > 1usize << Q {
            return Err("P256 adapter quotient width does not cover the claim".into());
        }
        Ok(Self { widths, bits })
    }
    pub(crate) fn shape(&self) -> TreeShape {
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

    /// Exponent chains, targets and (with `values`) the honest quotients.
    /// Both challenges must be independent, nonzero, uniform full prime-field
    /// samples drawn after the claim is fixed. This checks only that they are
    /// nonzero, so it is crate-private: outside tests, only `P256Mode` calls
    /// it, with the conversion it draws on entry.
    ///
    /// Bit `r` of a term with rescaled weight `A` has exponent
    /// `a_r = A * 2^r mod p`. Doubling modulo p subtracts p exactly when the
    /// correction bit `c_r` is set, so each leaf power follows from the
    /// previous one as `g^(a_(r+1)) = (g^(a_r))^2 * X^(c_r)`. This records
    /// the first power and the correction bits of every chain; the leaves
    /// are formed once the quotients are masked.
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
        let terms = claim.terms.len();
        let mut chains = [Vec::with_capacity(terms), Vec::with_capacity(terms)];
        // The honest quotients are prover-only; verifiers pass no values, and
        // verifier-only builds compile none of this accumulation. Each tree's
        // sum S of a_r over the set bits is kept modulo 2^64: as p = -1 modulo
        // 2^64, a_(r+1) = 2 a_r - c_r p gives the low limbs x_(r+1) = 2 x_r + c_r.
        #[cfg(any(test, feature = "prover"))]
        let mut sums = [0u64; 2];
        #[cfg(any(test, feature = "prover"))]
        let mut claim_sum = p.zero();
        for (j, (group, c)) in claim.terms.iter().enumerate() {
            let scaled = alpha.each_ref().map(|s| to_int(p, &p.mulf(s, c)));
            let term_chains = scaled.map(|coefficient| Chain {
                power: exponent(coefficient),
                digits: if group.width() == 1 {
                    [0; 4]
                } else {
                    integer::fraction_digits(&coefficient)
                },
            });
            #[cfg(any(test, feature = "prover"))]
            if let Some(v) = values {
                let value = to_int(p, &v[j]);
                let exceeds = !integer::fits_width(&value, group.width());
                #[cfg(test)]
                let exceeds = exceeds && !cheat::active();
                if exceeds {
                    return Err("P256 adapter value exceeds its group".into());
                }
                // A checked one-bit value is exactly zero or one, so its
                // contribution needs no prime-field multiplication.
                if group.width() == 1 {
                    if value[0] != 0 {
                        p.add(&mut claim_sum, c);
                    }
                } else {
                    p.add(&mut claim_sum, &p.mulf(c, &v[j]));
                }
                for tree in 0..2 {
                    let mut low = scaled[tree][0];

                    for r in 0..group.width() {
                        let set = 0u64.wrapping_sub(u64::from(integer::bit(&value, r)));
                        sums[tree] = sums[tree].wrapping_add(low & set);
                        if r + 1 < group.width() {
                            low =
                                (low << 1).wrapping_add(u64::from(term_chains[tree].correction(r)));
                        }
                    }
                }
            }
            for (tree, encoded_chain) in term_chains.into_iter().enumerate() {
                chains[tree].push(encoded_chain);
            }
        }
        // S is congruent to the rescaled claim's left side, so the claim holds
        // exactly when S = C modulo p. Then S >= 0 and C < p force S >= C, and
        // k = (S - C) / p is below the bit count, hence below 2^64: k is
        // C - S modulo 2^64.
        #[cfg(any(test, feature = "prover"))]
        let quotients = match values {
            Some(_) => {
                let unsatisfied = claim_sum != claim.target;
                #[cfg(test)]
                let unsatisfied = unsatisfied && !cheat::active();
                if unsatisfied {
                    return Err("P256 adapter unsatisfied claim".into());
                }
                let mut out = [Word::new(0)?; 2];
                for tree in 0..2 {
                    let quotient = targets[tree][0].wrapping_sub(sums[tree]);
                    #[cfg(test)]
                    let quotient = if cheat::active() {
                        quotient & ((1u64 << Q) - 1)
                    } else {
                        quotient
                    };
                    out[tree] = Word::new(quotient)?;
                }
                Some(out)
            }
            None => None,
        };
        Ok(P256Encoded {
            chains,
            bits: self.bits,
            targets: targets.map(exponent),
            #[cfg(any(test, feature = "prover"))]
            quotients,
        })
    }
}

/// One term's leaf powers in one tree: the first power `g^A` and the digits
/// of `A / p`, whose bit `255 - r` is the correction after leaf r.
#[derive(Clone, Copy)]
struct Chain {
    power: Gf2_128,
    digits: Int256,
}
impl Chain {
    #[inline(always)]
    fn correction(&self, r: usize) -> bool {
        let i = 255 - r;
        (self.digits[i / 64] >> (i % 64)) & 1 != 0
    }
}

/// Encoded claim: per tree and term, the leaf power chains; the root targets
/// and, for the prover only, the honest quotients.
pub(crate) struct P256Encoded<const Q: usize> {
    chains: [Vec<Chain>; 2],
    bits: usize,
    targets: [Gf2_128; 2],
    /// Honest quotients, computed only by provers.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) quotients: Option<[Word<Q>; 2]>,
}
impl<const Q: usize> P256Encoded<Q> {
    /// Visit each data leaf once, in claim order. Advancing four independent
    /// scalar chains overlaps their field-operation dependencies without
    /// changing the tree's order or its relation.
    fn visit_data_leaves(
        &self,
        tree: usize,
        claim: &ModularClaim<P256Element>,
        f: &Gf2_128Field,
        mut visit: impl FnMut(usize, Gf2_128),
    ) {
        const CHAINS: usize = 4;
        let x = f.u128_to_element(2);
        let mut scratch = [[f.zero(); CHAINS]; 256];
        for (terms, chains) in claim
            .terms
            .chunks(CHAINS)
            .zip(self.chains[tree].chunks(CHAINS))
        {
            let mut powers: [Gf2_128; CHAINS] =
                std::array::from_fn(|i| chains.get(i).map_or(f.one(), |chain| chain.power));
            let widths: [usize; CHAINS] =
                std::array::from_fn(|i| terms.get(i).map_or(0, |(group, _)| group.width()));
            let max_width = widths.iter().copied().max().unwrap_or(0);
            for (r, leaf_row) in scratch.iter_mut().enumerate().take(max_width) {
                for (i, chain) in chains.iter().enumerate() {
                    if r < widths[i] {
                        leaf_row[i] = powers[i];
                        if r + 1 < widths[i] {
                            powers[i] = f.mulf(&powers[i], &powers[i]);
                            if chain.correction(r) {
                                f.mul(&mut powers[i], &x);
                            }
                        }
                    }
                }
            }
            for (i, (group, _)) in terms.iter().enumerate() {
                for (r, leaf_row) in scratch.iter().enumerate().take(group.width()) {
                    visit(group.bit(r), leaf_row[i]);
                }
            }
        }
    }

    /// Emit the affine virtual inputs directly, without intermediate coefficient
    /// arrays or leaf trees. Each root target is folded into its first leaf.
    pub(crate) fn virtual_inputs(
        &self,
        claim: &ModularClaim<P256Element>,
        otp: &[BitGroup<Q>; 2],
        masked: &[MaskedWord<Q>; 2],
        f: &Gf2_128Field,
    ) -> Result<VirtualInputs<Gf2_128>, String> {
        if self
            .chains
            .iter()
            .any(|chains| chains.len() != claim.terms.len())
            || claim
                .terms
                .iter()
                .try_fold(0usize, |bits, (group, _)| bits.checked_add(group.width()))
                != Some(self.bits)
        {
            return Err("adapter tree shape".into());
        }
        let count = self
            .bits
            .checked_add(Q)
            .and_then(|n| n.checked_mul(2))
            .ok_or("adapter virtual input count overflow")?;
        let mut entries = Vec::with_capacity(count);
        let quotient_powers = P256Plan::<Q>::quotient_powers(f);
        let one = f.one();
        for tree in 0..2 {
            if f.is_zero(&self.targets[tree]) {
                return Err("adapter target must be nonzero".into());
            }
            let first = entries.len();
            self.visit_data_leaves(tree, claim, f, |source, power| {
                entries.push(VirtualInput {
                    source,
                    constant: one,
                    coefficient: f.subf(&power, &one),
                });
            });
            let inverse = f.invert(&self.targets[tree]);
            entries[first].constant = f.mulf(&entries[first].constant, &inverse);
            entries[first].coefficient = f.mulf(&entries[first].coefficient, &inverse);
            let pad = otp[tree].group();
            entries.extend(quotient_powers.iter().enumerate().map(|(j, &power)| {
                let leaf = Leaf::quotient(pad.bit(j), power, masked[tree].bit(j), f);
                VirtualInput {
                    source: leaf.source,
                    constant: leaf.constant,
                    coefficient: leaf.coefficient,
                }
            }));
        }
        Ok(VirtualInputs { entries })
    }

    /// Assemble unfurled trees for callers that need their explicit roots.
    /// Proof drivers use `virtual_inputs` to avoid these intermediate arrays.
    #[cfg(test)]
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
                let mut leaves = Vec::with_capacity(self.bits + Q);
                self.visit_data_leaves(tree, claim, f, |source, power| {
                    leaves.push(Leaf::data(source, f.subf(&power, &f.one()), f));
                });
                let pad = otp[tree].group();
                leaves.extend(
                    powers.iter().enumerate().map(|(j, &power)| {
                        Leaf::quotient(pad.bit(j), power, masked[tree].bit(j), f)
                    }),
                );
                TreeInstance {
                    leaves,
                    target: self.targets[tree],
                }
            })
            .collect()
    }
}

#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::runtime::v2::foreign) use transcript::conversion;

/// The P-256 wrapping mode as an adapter mode: two trees, each with a
/// `Word<Q>` quotient published as `MaskedWord<Q>` over a committed `Otp<Q>`.
///
/// The adapter's conversion pair and masked quotients enter the transcript
/// only through the mode: `draw_conversion` stamps the pair as the mode's
/// input challenge and `prove` and `verify` send the quotients. The raw
/// steps are not public:
///
/// ```compile_fail,E0432
/// use longfellow_zk::runtime::v2::foreign::adapter::p256::conversion;
/// ```
///
/// ```compile_fail,E0603
/// use longfellow_zk::runtime::v2::foreign::adapter::p256::send_quotients;
/// ```
pub(crate) struct P256Mode<const Q: usize> {
    plan: P256Plan<Q>,
    otp: [BitGroup<Q>; 2],
    shape: TreeShape,
    /// `shape.virtual_inputs()`, checked when the fragment was built.
    virtual_inputs: usize,
    fragment: Circuit<Gf2_128Field>,
}
impl<const Q: usize> super::AdapterMode<P256Field> for P256Mode<Q> {
    const MASK_BITS: usize = 256;
    /// Below the 256-bit length of p: no group holds an integer `>= p`.
    const MAX_VALUE_BITS: usize = 255;
    type Pads = [crate::runtime::v2::foreign::word::Otp<Q>; 2];
    type Message = [MaskedWord<Q>; 2];
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
        reserved: &mut crate::runtime::v2::foreign::reserved::ReservedWitness<'_>,
    ) -> Result<(), String> {
        for (group, pad) in self.otp.iter().zip(pads) {
            reserved.set(group.group(), pad.bits())?;
        }
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn prove(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<P256Element>,
        values: &[P256Element],
        pads: Self::Pads,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<(Self::Message, VirtualInputs<Gf2_128>), String> {
        let mode = t.part();
        let Conversion(alpha) = transcript::draw_conversion(&mut t.transcript(), p);
        let encoded = mode.plan.encode(claim, &alpha, Some(values), p, f)?;
        let k = encoded.quotients.ok_or("P256 adapter quotients")?;
        let [o0, o1] = pads;
        let masked = [MaskedWord::mask(k[0], o0), MaskedWord::mask(k[1], o1)];
        send_quotients(&mut t.transcript(), &masked);
        let leaves = encoded.virtual_inputs(claim, &mode.otp, &masked, f)?;
        Ok((masked, leaves))
    }
    #[cfg(any(test, feature = "verifier"))]
    fn verify(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<P256Element>,
        masked: &Self::Message,
        p: &P256Field,
        f: &Gf2_128Field,
    ) -> Result<VirtualInputs<Gf2_128>, String> {
        let mode = t.part();
        let Conversion(alpha) = transcript::draw_conversion(&mut t.transcript(), p);
        let encoded = mode.plan.encode(claim, &alpha, None, p, f)?;
        send_quotients(&mut t.transcript(), masked);
        encoded.virtual_inputs(claim, &mode.otp, masked, f)
    }
}

#[cfg(test)]
mod tests;
