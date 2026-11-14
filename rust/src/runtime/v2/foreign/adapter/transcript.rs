// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Transcript rounds of the P-256 adapter: conversion challenges and the
//! masked quotients. Derived leaf coefficients are never absorbed.
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::p256::{P256Element, P256Field},
        v2::{foreign::word::MaskedWord, proto::RoundLabel, transcript::TranscriptRef},
    },
};

/// Two independent nonzero full-field conversion challenges. Wrapping mode
/// needs both: one rescaling leaves a false claim about 2^-117 to survive.
pub fn conversion(t: &mut TranscriptRef<'_>, p: &P256Field) -> [P256Element; 2] {
    t.round(RoundLabel::Conversion, |mut w| {
        w.write_bytes(b"p256-adapter/two-independent-full-field-rescalings/v3");
        let mut r = w.begin_squeeze();
        let value = std::array::from_fn(|_| loop {
            let a = r.elt_field(p);
            if !p.is_zero(&a) {
                break a;
            }
        });
        r.end_round(value)
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
