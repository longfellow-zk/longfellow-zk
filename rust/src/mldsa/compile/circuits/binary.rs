// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    sample::{
        allocate_witness_with_keccak as sample_witness, assert_sample_in_ball_bits,
        SampleInBallWitness,
    },
    shake::{allocate_witness_with_keccak as shake_witness, Shake256, Shake256Witness},
    shared::Shared,
};
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::{BitvecIO, BitvecLogic, V8},
        boolean::{Bitw, Boolean},
    },
    compile::{
        algebra::gf2_128::Gf2_128Field,
        logic::{Logic, LogicIO},
    },
    mldsa::proto::{BinaryKeccak, MlDsaParams, N},
};

#[cfg(test)]
mod tests;

pub(crate) struct BinaryWitness<L: LogicIO> {
    pub shared: Shared<L>,
    challenge: Vec<V8<L>>,
    sample: SampleInBallWitness<L>,
    hash_witness: Shake256Witness<L>,
    mu: Vec<V8<L>>,
}
impl<L: LogicIO> BinaryWitness<L> {
    pub(crate) fn permutation_links(&self, logic: &L) -> Vec<(Vec<usize>, Vec<usize>)> {
        let mut out = self.sample.shake.links(logic);
        out.extend(self.hash_witness.links(logic));
        out
    }
}

pub(crate) fn allocate_private<L: LogicIO, P: MlDsaParams>(
    logic: &L,
    pos: &mut usize,
    keccak: BinaryKeccak,
) -> BinaryWitness<L> {
    let shared = Shared::input::<P>(logic, pos);
    let bv = BitvecLogic::new(logic);
    let io = BitvecIO::new(&bv);
    let challenge = (0..P::C_TILDE_BYTES).map(|_| io.next(pos)).collect();
    let sample = sample_witness::<_, P>(&bv, pos, keccak);
    let hash_witness = shake_witness(&bv, pos, 64 + P::K * P::W1_BYTES, P::C_TILDE_BYTES, keccak);
    let mu = (0..64).map(|_| io.next(pos)).collect();
    BinaryWitness {
        shared,
        challenge,
        sample,
        hash_witness,
        mu,
    }
}

pub(crate) fn signature_assertions<L: LogicIO<F = Gf2_128Field>, P: MlDsaParams>(
    logic: &L,
    witness: BinaryWitness<L>,
    keccak: BinaryKeccak,
) -> Vec<L::Assertions> {
    let BinaryWitness {
        shared,
        challenge,
        sample,
        hash_witness,
        mu,
    } = witness;
    let bv = BitvecLogic::new(logic);
    let boolean = Boolean::new(logic);
    let arithmetic = Arithmetic::new(logic);
    let mut assertions = Vec::new();
    let constant = |width, value: u64| -> Vec<Bitw<_>> {
        (0..width)
            .map(|i| boolean.konst((value >> i) & 1 != 0))
            .collect()
    };
    assertions.push(assert_sample_in_ball_bits::<_, P>(
        logic,
        &challenge,
        &sample,
        &shared.positive,
        &shared.negative,
    ));
    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    for bits in shared.z.iter().flatten() {
        assertions.push(boolean.assert_true(
            "z_norm",
            &arithmetic.leq(bits, &constant(P::Z_BITS, u64::from(2 * bound - 2))),
        ));
    }
    let max_high = constant(P::R1_BITS, u64::from(P::use_hint_modulus() - 1));
    for row in 0..P::K {
        for i in 0..N {
            for bits in [&shared.raw[row][i], &shared.hinted[row][i]] {
                assertions
                    .push(boolean.assert_true("high_range", &arithmetic.leq(bits, &max_high)));
            }
            let aux = &shared.auxiliary[row][i];
            let low = &aux[..P::r0_bits()];
            assertions.push(boolean.assert_true(
                "canonical_rounding",
                &boolean.impliesb(
                    &arithmetic.is_zero(low),
                    &arithmetic.is_zero(&shared.raw[row][i]),
                ),
            ));
            assertions.push(boolean.assert_true(
                "remainder_range",
                &arithmetic.leq(low, &constant(P::r0_bits(), u64::from(2 * P::GAMMA2))),
            ));
            assertions.push(boolean.assert_eq(
                "remainder_sign",
                &aux[P::r0_bits()],
                &arithmetic.leq(low, &constant(P::r0_bits(), u64::from(P::GAMMA2))),
            ));
            assertions.push(assert_hint_relation::<_, P>(
                logic,
                &shared.h[row][i][0],
                &shared.raw[row][i],
                &aux[P::r0_bits()],
                &shared.hinted[row][i],
            ));
        }
    }
    // Full-width integer cardinality, without overflow before comparison.
    let width = (P::K * N).ilog2() as usize + 1;
    let mut counts: Vec<_> = shared
        .h
        .iter()
        .flatten()
        .map(|bits| boolean.zext(bits, width))
        .collect();
    while counts.len() > 1 {
        let mut next: Vec<_> = counts
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| arithmetic.unchecked_add(&pair[0], &pair[1]).0)
            .collect();
        next.extend(counts.as_chunks::<2>().1.iter().cloned());
        counts = next;
    }
    assertions.push(boolean.assert_true(
        "hint_weight",
        &arithmetic.leq(&counts[0], &constant(width, P::OMEGA as u64)),
    ));
    let encoding_bits: Vec<_> = shared.hinted.iter().flatten().flatten().cloned().collect();
    let encoded: Vec<V8<_>> = encoding_bits
        .as_chunks::<8>()
        .0
        .iter()
        .map(|bits| V8::new(bits.to_vec()))
        .collect();
    assert_eq!(encoded.len(), P::K * P::W1_BYTES);
    let mut hash_input = mu;
    hash_input.extend(encoded);
    let (computed, hash_assertions) = Shake256::with_keccak(logic, keccak).assert_hash(
        &hash_input,
        P::C_TILDE_BYTES,
        &hash_witness,
    );
    assertions.push(hash_assertions);
    for (actual, expected) in computed.iter().zip(&challenge) {
        assertions.push(bv.assert_eq("challenge_hash", actual, expected));
    }
    assertions
}

/// FIPS 204 UseHint on bounded high-part bits, after sign and canonical
/// decomposition checks. Compact placement keeps this entire relation binary.
pub(crate) fn assert_hint_relation<L: Logic, P: MlDsaParams>(
    logic: &L,
    hint: &Bitw<L>,
    raw: &[Bitw<L>],
    nonpositive: &Bitw<L>,
    hinted: &[Bitw<L>],
) -> L::Assertions {
    let boolean = Boolean::new(logic);
    let arithmetic = Arithmetic::new(logic);
    let constant = |value: u32| {
        (0..P::R1_BITS)
            .map(|i| boolean.konst(value >> i & 1 != 0))
            .collect::<Vec<_>>()
    };
    assert_eq!(raw.len(), P::R1_BITS);
    assert_eq!(hinted.len(), P::R1_BITS);
    // Share the direction and endpoint predicates, as in GordieHowe's UseHint
    // gadget. A single carry/borrow chain adds h*(1-2*nonpositive) modulo 2^w.
    let mut carry = hint.clone();
    let mut expected = Vec::with_capacity(P::R1_BITS);
    for (index, bit) in raw.iter().enumerate() {
        expected.push(boolean.xorb(bit, &carry));
        if index + 1 < P::R1_BITS {
            carry = boolean.andb(&carry, &boolean.xorb(bit, nonpositive));
        }
    }
    let modulus = P::use_hint_modulus();
    let binary_modulus = 1u32 << P::R1_BITS;
    assert!(modulus <= binary_modulus);
    if modulus != binary_modulus {
        let wrap_up = boolean.andb(
            &boolean.andb(hint, &boolean.notb(nonpositive)),
            &arithmetic.eqb(raw, &constant(modulus - 1)),
        );
        let wrap_down = boolean.andb(&boolean.andb(hint, nonpositive), &arithmetic.is_zero(raw));
        // At the two endpoints, correct the binary wrap with fixed XOR masks.
        // For ML-DSA-65, M=16 already matches the four-bit binary modulus.
        let down_mask = (binary_modulus - 1) ^ (modulus - 1);
        for (index, bit) in expected.iter_mut().enumerate() {
            if modulus >> index & 1 != 0 {
                *bit = boolean.xorb(bit, &wrap_up);
            }
            if down_mask >> index & 1 != 0 {
                *bit = boolean.xorb(bit, &wrap_down);
            }
        }
    }
    arithmetic.assert_eq("hint_correction", hinted, &expected)
}
