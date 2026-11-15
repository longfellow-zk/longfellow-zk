// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript rounds of the P-256 adapter: conversion challenges and the
//! masked quotients. Derived leaf coefficients are never absorbed.
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::p256::{P256Element, P256Field},
        v2::{
            foreign::word::MaskedWord,
            proto::RoundLabel,
            transcript::{Bound, Challenge, RoundEnd, TranscriptRef, Writing},
        },
    },
};

/// The P-256 adapter's conversion pair, each nonzero. Only its draw
/// (`draw_conversion`) builds it.
pub struct Conversion(pub(super) [P256Element; 2]);
impl Conversion {
    pub fn values(&self) -> &[P256Element; 2] {
        &self.0
    }
}

fn conversion_round<'r, T>(
    mut w: Writing<'r>,
    p: &P256Field,
    wrap: impl FnOnce([P256Element; 2]) -> T,
) -> RoundEnd<'r, T> {
    w.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v3");
    let mut r = w.begin_squeeze();
    let value = std::array::from_fn(|_| loop {
        let a = r.elt_field(p);
        if !p.is_zero(&a) {
            break a;
        }
    });
    r.end_round(wrap(value))
}

/// Two independent nonzero full-field conversion challenges. Wrapping mode
/// needs both: one rescaling leaves a false claim about 2^-117 to survive.
pub fn conversion(t: &mut TranscriptRef<'_>, p: &P256Field) -> [P256Element; 2] {
    t.round(RoundLabel::Conversion, |w| conversion_round(w, p, |x| x))
}

/// The same round as `conversion`, drawn as the adapter's input challenge.
pub(super) fn draw_conversion<P: ?Sized>(
    t: &mut Bound<'_, P>,
    p: &P256Field,
) -> Challenge<Conversion> {
    t.challenge(RoundLabel::Conversion, |w| {
        conversion_round(w, p, Conversion)
    })
}

/// Bind both masked quotients, in their canonical encodings, before the
/// binary sumcheck. Their width is fixed by the instance type.
pub fn absorb_masked<const Q: usize>(t: &mut TranscriptRef<'_>, masked: &[MaskedWord<Q>; 2]) {
    t.absorb(|w| {
        w.write_bytes(b"p256-adapter/masked-quotient-bits/v1");
        for m in masked {
            w.write_bytes(&m.encoded());
        }
    });
}
