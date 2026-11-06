// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 adapter layout binding, conversion challenges and masked quotient advice.
use crate::{
    core::algebra::AlgebraicField,
    mdoc::circuits::p256_adapter::{Encoded, Plan, SHARED_BITS},
    runtime::{
        algebra::{
            gf2_128::Gf2_128,
            p256::{P256Element, P256Field},
        },
        v2::transcript::Transcript,
    },
};

pub(super) fn bind_prime(t: &mut Transcript, circuit_id: &[u8; 32], shared: usize) {
    t.bind(|w| {
        w.write_bytes(b"native-shared-prefix/joint/v1");
        w.write_bytes(circuit_id);
    });
    t.bind(|w| w.write_bytes(&(shared as u64).to_le_bytes()));
}

pub(super) fn bind_binary(t: &mut Transcript, template_id: &[u8; 32], logw_layers: &[usize]) {
    t.bind(|w| {
        w.write_bytes(b"mdoc/adapter/shared-binary/v1");
        w.write_bytes(template_id);
    });
    for &width in logw_layers {
        t.bind(|w| w.write_bytes(&(width as u64).to_le_bytes()));
    }
}

pub(crate) fn eta(t: &mut Transcript, p: &P256Field) -> P256Element {
    t.round(
        crate::runtime::v2::transcript::RoundLabel::Rescaling,
        |mut w| {
            w.write_bytes(b"native-shared-prefix/nonzero-rescaling/v2");
            let mut r = w.begin_squeeze();
            let value = loop {
                let x = r.elt_field(p);
                if !p.is_zero(&x) {
                    break x;
                }
            };
            r.end_round(value)
        },
    )
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
    t.bind(|w| {
        w.write_bytes(b"native-shared-prefix/fixed-masked-opening/v1");
        w.write_elt_field_slice(&weights, p);
    });
    t.bind(|w| w.write_elt_field(mu, p));
    Ok(weights)
}
pub(crate) fn alphas(t: &mut Transcript, p: &P256Field) -> [P256Element; 2] {
    t.round(
        crate::runtime::v2::transcript::RoundLabel::Conversion,
        |mut w| {
            w.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v3");
            let mut r = w.begin_squeeze();
            let value = std::array::from_fn(|_| loop {
                let a = r.elt_field(p);
                if !p.is_zero(&a) {
                    break a;
                }
            });
            r.end_round(value)
        },
    )
}
pub(crate) fn public(
    plan: &Plan,
    encoded: Encoded,
    masked: &[u8],
    t: &mut Transcript,
) -> Result<Vec<Gf2_128>, String> {
    plan.validate_advice(masked)?;
    t.bind(|w| {
        w.write_bytes(b"p256-adapter/masked-quotient-bits/v1");
        w.write_bytes(masked);
    });
    let mut values = Vec::with_capacity(plan.public_count());
    values.extend(encoded.coefficients);
    values.extend(
        (0..plan.advice_bits()).map(|r| Gf2_128::from(u128::from((masked[r / 8] >> (r % 8)) & 1))),
    );
    values.extend(encoded.targets);
    Ok(values)
}

#[cfg(test)]
#[path = "../../../tests/v2_adapter_transcript.rs"]
mod tests;
