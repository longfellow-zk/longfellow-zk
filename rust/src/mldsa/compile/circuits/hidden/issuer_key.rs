// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! SHAKE128 expansion and stable rejection filtering via two multiset products.
//! This is a direct permutation argument, with no lookup/logarithmic derivative.
#[cfg(test)]
mod tests;
use crate::{
    circuits::{
        arithmetic::Arithmetic,
        bitvec::{BitvecIO, BitvecLogic},
        boolean::{Bitw, Boolean, BooleanIO},
    },
    compile::{
        algebra::gf2_128::Gf2_128Field,
        logic::{Eltw, Logic, LogicIO},
    },
    core::algebra::fp24::Q,
    mldsa::{
        compile::{
            circuits::shake::{allocate_witness_with_rate, Shake256},
            key_bits,
        },
        proto::{BinaryKeccak, MlDsaParams, N, REJ_NTT_BYTES},
    },
};

pub(crate) fn tree<L: Logic>(l: &L, mut values: Vec<Eltw<L>>) -> Eltw<L> {
    assert!(!values.is_empty());
    while values.len() > 1 {
        let mut next: Vec<_> = values
            .as_chunks::<2>()
            .0
            .iter()
            .map(|v| l.precious(&l.mul(&v[0], &v[1])))
            .collect();
        next.extend_from_slice(values.as_chunks::<2>().1);
        values = next;
    }
    values.pop().unwrap()
}
pub(crate) fn allocate_issuer_key<L: LogicIO<F = Gf2_128Field>, P: MlDsaParams>(
    l: &L,
    pos: &mut usize,
    gamma: &[Eltw<L>],
    keccak: BinaryKeccak,
) -> (
    Vec<Bitw<L>>,
    Vec<L::Assertions>,
    Vec<(Vec<usize>, Vec<usize>)>,
) {
    assert_eq!(gamma.len(), 2);
    let b = Boolean::new(l);
    let io = BooleanIO::new(l);
    let a = Arithmetic::new(l);
    let bv = BitvecLogic::new(l);
    let key_bits: Vec<_> = (0..key_bits::<P>()).map(|_| io.next(pos)).collect();
    let rho: Vec<_> = (0..32).map(|_| BitvecIO::new(&bv).next(pos)).collect();
    let constant =
        |n: usize, x: usize| -> Vec<_> { (0..n).map(|r| b.konst(x >> r & 1 != 0)).collect() };
    let polynomial_bits = (usize::BITS - (P::K * P::L - 1).leading_zeros()) as usize;
    let tag = |value: &[Bitw<L>], index: &[Bitw<L>], poly: usize| {
        let mut bits = value.to_vec();
        bits.extend_from_slice(index);
        bits.extend(constant(polynomial_bits, poly));
        a.as_eltw_field(&bits)
    };
    let mut input = [Vec::new(), Vec::new()];
    let mut output = [Vec::new(), Vec::new()];
    let mut assertions = Vec::new();
    let mut links = Vec::new();
    for poly in 0..P::K * P::L {
        let mut seed = rho.clone();
        seed.push(bv.of_u64((poly % P::L) as u64));
        seed.push(bv.of_u64((poly / P::L) as u64));
        let witness = allocate_witness_with_rate(&bv, pos, 34, REJ_NTT_BYTES, keccak, 168);
        links.extend(witness.links(l));
        let (bytes, ok) = Shake256::shake128(l, keccak).assert_hash(&seed, REJ_NTT_BYTES, &witness);
        assertions.push(ok);
        let mut previous = constant(9, 0);
        for chunk in bytes.as_chunks::<3>().0 {
            let mut value = chunk[0].as_array().to_vec();
            value.extend_from_slice(chunk[1].as_array());
            value.extend_from_slice(&chunk[2].as_array()[..7]);
            let valid = a.lt(&value, &constant(23, Q as usize));
            let next: Vec<_> = (0..9).map(|_| io.next(pos)).collect();
            let mut step = constant(9, 0);
            step[0] = valid.clone();
            assertions.push(a.assert_eq(
                "rejection_count",
                &next,
                &a.unchecked_add(&previous, &step).0,
            ));
            let keep = b.andb(&valid, &b.notb(&previous[8]));
            let tagged = l.precious(&l.mul(&b.as_eltw(&keep), &tag(&value, &previous[..8], poly)));
            for tree in 0..2 {
                input[tree].push(l.precious(&l.add(&gamma[tree], &tagged)));
            }
            previous = next;
        }
        assertions.push(b.assert_true("enough_key_coefficients", &previous[8]));
        for i in 0..N {
            let value = &key_bits[(poly * N + i) * 23..(poly * N + i + 1) * 23];
            let tagged = tag(value, &constant(8, i), poly);
            for tree in 0..2 {
                output[tree].push(l.precious(&l.add(&gamma[tree], &tagged)));
            }
        }
        for _ in N..REJ_NTT_BYTES / 3 {
            for tree in 0..2 {
                output[tree].push(gamma[tree].clone());
            }
        }
    }
    for (left, right) in input.into_iter().zip(output) {
        assertions.push(l.assert_eq("key_expansion_permutation", &tree(l, left), &tree(l, right)));
    }
    (key_bits, assertions, links)
}
