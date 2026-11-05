// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Independent conversion challenges and canonically masked quotient advice.
use super::Plan;
pub(crate) use super::{shared_plan as plan, SHARED_BITS};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            gf2_128::Gf2_128,
            p256::{P256Element, P256Field},
        },
        random::{RandomEngine, Transcript},
    },
};
pub(crate) fn eta(t: &mut Transcript, p: &P256Field) -> P256Element {
    t.write_bytes(b"native-shared-prefix/nonzero-rescaling/v1");
    loop {
        let x = t.elt_field(p);
        if !p.is_zero(&x) {
            return x;
        }
    }
}
pub(crate) fn weights(
    a: &[P256Element],
    eta: &P256Element,
    mu: &P256Element,
    t: &mut Transcript,
    p: &P256Field,
) -> Result<Vec<P256Element>, String> {
    if a.len() < SHARED_BITS {
        return Err("adapter shared weights".into());
    }
    let mut weights: Vec<_> = a[..SHARED_BITS].iter().map(|a| p.mulf(eta, a)).collect();
    weights.push(p.one());
    t.write_bytes(b"native-shared-prefix/fixed-masked-opening/v1");
    t.write_elt_field_slice(&weights, p);
    t.write_elt_field(mu, p);
    Ok(weights)
}
pub(crate) fn alphas(t: &mut Transcript, p: &P256Field) -> [P256Element; 2] {
    t.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v2");
    std::array::from_fn(|_| loop {
        let a = t.elt_field(p);
        if !p.is_zero(&a) {
            return a;
        }
    })
}
pub(crate) fn public(
    plan: &Plan,
    encoded: super::Encoded<Gf2_128>,
    masked: &[u8],
    t: &mut Transcript,
) -> Result<Vec<Gf2_128>, String> {
    if masked.len() != plan.advice_bytes()
        || (plan.advice_bits() % 8 != 0
            && masked[masked.len() - 1] >> (plan.advice_bits() % 8) != 0)
    {
        return Err("adapter noncanonical quotient advice".into());
    }
    t.write_bytes(b"p256-adapter/masked-quotient-bits/v1");
    t.write_bytes(masked);
    let mut values = Vec::with_capacity(plan.public_count());
    values.extend(encoded.coefficients);
    values.extend(
        (0..plan.advice_bits()).map(|r| Gf2_128::from(u128::from((masked[r / 8] >> (r % 8)) & 1))),
    );
    values.extend(encoded.targets);
    Ok(values)
}
