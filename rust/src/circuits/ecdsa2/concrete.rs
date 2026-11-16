// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::shape::{Derived, Given, Slicing};
use crate::{
    circuits::ec::{Pt2, Pt3},
    core::algebra::{
        ec as ec_concrete, ec::Curve, AlgebraicField, HasLookupPoints, Nat, NatOf,
        SupportsNatConversions,
    },
};

#[cfg(test)]
mod tests;

pub fn given<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    pkxy: &(F::E, F::E),
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Given<F::E> {
    // Legacy callers retain their infallible API and witness representation.
    try_given(curve, pkxy, e, r, s, f, fn_field).expect("Cannot invert zero")
}

/// Fallible construction for v2: malformed or unsupported signatures must not
/// unwind while the application is preparing a witness.
pub(super) fn try_given<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    pkxy: &(F::E, F::E),
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Result<Given<F::E>, &'static str> {
    let s_fn = fn_field.reduce_nat(s);
    let s_inv = checked_inverse(fn_field, &s_fn)?;
    let e_fn = fn_field.reduce_nat(e);
    let r_fn = fn_field.reduce_nat(r);
    let te_s = fn_field.mulf(&e_fn, &s_inv);
    let tr_s = fn_field.mulf(&r_fn, &s_inv);
    let nes = fn_field.to_nat(&te_s);
    let nrs = fn_field.to_nat(&tr_s);

    let g = ec_concrete::projective(curve, f, curve.g());
    let pk = ec_concrete::projective(curve, f, pkxy);

    let nes_g = ec_concrete::scalar_mul(curve, f, 256, &nes, &g);
    let nrs_pk = ec_concrete::scalar_mul(curve, f, 256, &nrs, &pk);

    let r_proj = ec_concrete::add(curve, f, &nes_g, &nrs_pk);

    let rx = f.reduce_nat(r);
    let ry = f.mulf(&r_proj.1, &checked_inverse(f, &r_proj.2)?);

    let order_neg_s = fn_field.neg(&s_fn);
    let nms_nat = fn_field.to_nat(&order_neg_s);

    let e_bits = e.to_bits(256);
    let rx_bits = r.to_bits(256);
    let nms_bits = nms_nat.to_bits(256);

    let ers = std::array::from_fn(|i| {
        let idx =
            (usize::from(e_bits[i]) * 4) + (usize::from(rx_bits[i]) * 2) + usize::from(nms_bits[i]);
        f.lookup_point(9, idx)
    });

    Ok(Given {
        pkxy: pkxy.clone(),
        e: f.reduce_nat(e),
        rxy: (rx, ry),
        ers,
    })
}

pub fn derived<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    pkxy: &(F::E, F::E),
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Derived<F::E> {
    try_derived(curve, pkxy, e, r, s, f, fn_field).expect("Cannot invert zero")
}

/// Keep the existing affine witness layout, but reject its exceptional points
/// explicitly. In particular G+PK may be infinity even for a valid signature.
pub(super) fn try_derived<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    pkxy: &(F::E, F::E),
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Result<Derived<F::E>, &'static str> {
    let given = try_given(curve, pkxy, e, r, s, f, fn_field)?;
    derived_from_given(curve, &given, e, r, s, f, fn_field)
}

/// Construct both parts together so the verification point is recovered once.
/// Separate legacy constructors retain their APIs and serialized values.
pub fn try_witness<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    pkxy: &(F::E, F::E),
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Result<(Given<F::E>, Derived<F::E>), &'static str> {
    let given = try_given(curve, pkxy, e, r, s, f, fn_field)?;
    let derived = derived_from_given(curve, &given, e, r, s, f, fn_field)?;
    Ok((given, derived))
}

fn derived_from_given<
    const W: usize,
    F: AlgebraicField + SupportsNatConversions<W> + HasLookupPoints,
    Fn: AlgebraicField + SupportsNatConversions<W, N = F::N>,
    C: Curve<W, F = F, N = F::N>,
>(
    curve: &C,
    given: &Given<F::E>,
    e: &NatOf<W, F>,
    r: &NatOf<W, F>,
    s: &NatOf<W, F>,
    f: &F,
    fn_field: &Fn,
) -> Result<Derived<F::E>, &'static str> {
    let g = ec_concrete::projective(curve, f, curve.g());
    let pk = ec_concrete::projective(curve, f, &given.pkxy);
    let r_pt = ec_concrete::projective(curve, f, &given.rxy);

    let g_pk_proj = ec_concrete::add(curve, f, &g, &pk);
    let g_r_proj = ec_concrete::add(curve, f, &g, &r_pt);
    let pk_r_proj = ec_concrete::add(curve, f, &pk, &r_pt);

    let g_pk = checked_affine(f, &g_pk_proj)?;
    let g_r = checked_affine(f, &g_r_proj)?;
    let pk_r = checked_affine(f, &pk_r_proj)?;

    let pk_r_projective = ec_concrete::projective(curve, f, &pk_r);
    let g_pk_r_proj = ec_concrete::add(curve, f, &g, &pk_r_projective);
    let g_pk_r = checked_affine(f, &g_pk_r_proj)?;

    let order_neg_s = fn_field.neg(&fn_field.reduce_nat(s));
    let nms_nat = fn_field.to_nat(&order_neg_s);

    let e_bits = e.to_bits(256);
    let rx_bits = r.to_bits(256);
    let nms_bits = nms_nat.to_bits(256);

    let opts = [
        ec_concrete::zero(f),
        r_pt.clone(),
        pk.clone(),
        pk_r_projective,
        g.clone(),
        ec_concrete::projective(curve, f, &g_r),
        ec_concrete::projective(curve, f, &g_pk),
        ec_concrete::projective(curve, f, &g_pk_r),
    ];

    let mut round = std::array::from_fn(|_| ec_concrete::zero(f));
    let mut p = ec_concrete::zero(f);
    for i in (0..256).rev() {
        let idx =
            (usize::from(e_bits[i]) * 4) + (usize::from(rx_bits[i]) * 2) + usize::from(nms_bits[i]);
        let b = &opts[idx];
        let sum_val = ec_concrete::add(curve, f, &ec_concrete::double(curve, f, &p), b);
        p = sum_val;
        round[i] = p.clone();
    }

    let pkxinv = checked_inverse(f, &given.pkxy.0)?;
    let rxinv = checked_inverse(f, &given.rxy.0)?;
    let nms_val = f.reduce_nat(&nms_nat);
    let nmsinv = checked_inverse(f, &nms_val)?;
    let yinv = checked_inverse(f, &p.1)?;

    Ok(Derived {
        pkxinv,
        rxinv,
        nmsinv,
        yinv,
        slicing: Slicing {
            g_pk,
            g_r,
            pk_r,
            g_pk_r,
            round,
        },
    })
}

fn checked_inverse<F: AlgebraicField>(f: &F, value: &F::E) -> Result<F::E, &'static str> {
    if f.is_zero(value) {
        Err("Signature requires an unsupported zero inversion")
    } else {
        Ok(f.invert(value))
    }
}

fn checked_affine<F: AlgebraicField>(f: &F, point: &Pt3<F::E>) -> Result<Pt2<F::E>, &'static str> {
    let inverse = checked_inverse(f, &point.2)?;
    Ok((f.mulf(&point.0, &inverse), f.mulf(&point.1, &inverse)))
}
