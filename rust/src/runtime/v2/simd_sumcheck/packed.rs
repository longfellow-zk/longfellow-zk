// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Lane contractions on packed bit planes, before expanding into field tables.
use super::*;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::algebra::RuntimeField,
};
fn shift(x: u128, amount: isize) -> u128 {
    if amount >= 0 {
        x << (amount as usize)
    } else {
        x >> ((-amount) as usize)
    }
}
pub(super) fn packed_round(
    terms: &[Product],
    words: &[E],
    a: &[E],
    m: &[E],
    f: &F,
) -> RoundPoly<F> {
    // m contains monomials in the challenges already bound within a lane.
    // Shifts align each pair of those coordinates while masks retain its
    // original polynomial-basis weight. Compute c0 and the cross coefficient;
    // the incoming projective claim supplies the omitted quadratic coefficient.
    let s = m.len();
    let mut c0 = f.zero();
    let mut c1 = f.zero();
    for i in 0..s {
        for k in 0..s {
            let mask = (0..128)
                .step_by(2 * s)
                .fold(0u128, |v, b| v | (1u128 << (b + k)));
            let mut accum0 = f.zero_accum();
            let mut accum1 = f.zero_accum();
            for t in terms {
                let x = words[t.l].to_u128();
                let y = words[t.r].to_u128();
                let p0 = shift(x, k as isize - i as isize) & y & mask;
                let p1 = (shift(x, (s + k) as isize - i as isize) & y & (mask << s))
                    ^ (shift(x, k as isize - (s + i) as isize) & y & mask);
                f.mac(&mut accum0, &a[t.g], &E::from(p0));
                f.mac(&mut accum1, &a[t.g], &E::from(p1));
            }
            let scale = f.mulf(&m[i], &m[k]);
            f.fma(&mut c0, &scale, &f.accum_reduce(&accum0));
            f.fma(&mut c1, &scale, &f.accum_reduce(&accum1));
        }
    }
    RoundPoly {
        coefficients: [c0, c1],
    }
}

pub(super) fn quad_round_poly<F: RuntimeField + SerializableField>(
    q_l: &[F::E],
    w: &[F::E],
    claim: &F::E,
    f: &F,
) -> RoundPoly<F> {
    assert_eq!(q_l.len(), w.len());
    let n = q_l.len();
    let pairs = n / 2;
    let mut accum_c0 = f.zero_accum();
    let mut accum_p1 = f.zero_accum();

    for i in 0..pairs {
        let idx = 2 * i;
        f.mac(&mut accum_c0, &q_l[idx], &w[idx]);
        let q_sum = f.addf(&q_l[idx], &q_l[idx + 1]);
        let w_sum = f.addf(&w[idx], &w[idx + 1]);
        f.mac(&mut accum_p1, &q_sum, &w_sum);
    }

    if !n.is_multiple_of(2) {
        // With zero odd coefficients, the unpaired product is constant in x
        // and contributes equally to c0 and p(1).
        let last = n - 1;
        f.mac(&mut accum_c0, &q_l[last], &w[last]);
        f.mac(&mut accum_p1, &q_l[last], &w[last]);
    }

    let c0 = f.accum_reduce(&accum_c0);
    let p1 = f.accum_reduce(&accum_p1);
    // p(1) = c0 + c1 + c2; subtract claim = c0 + c2 to isolate c1.
    let c1 = f.subf(&p1, claim);
    RoundPoly {
        coefficients: [c0, c1],
    }
}
