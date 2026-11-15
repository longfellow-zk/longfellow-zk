// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::core::algebra::AlgebraicField;

/// An explicit coordinate encoding `x = scale * b + offset`, where `b` is
/// the unsigned integer stored in the coordinate's bit group.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct AffineEncoding {
    pub scale: i64,
    pub offset: i64,
}
impl AffineEncoding {
    pub(crate) const IDENTITY: Self = Self {
        scale: 1,
        offset: 0,
    };

    #[cfg(any(test, feature = "mdoc"))]
    pub(crate) fn new(scale: i64, offset: i64) -> Result<Self, String> {
        if scale == 0 {
            return Err("zero affine coordinate scale".into());
        }
        Ok(Self { scale, offset })
    }

    pub(super) fn coefficients<F: AlgebraicField>(&self, f: &F) -> Result<(F::E, F::E), String> {
        let scale = signed_integer(self.scale, f);
        if f.is_zero(&scale) {
            return Err("affine coordinate scale vanishes in this field".into());
        }
        Ok((scale, signed_integer(self.offset, f)))
    }
}

fn signed_integer<F: AlgebraicField>(integer: i64, f: &F) -> F::E {
    let mut magnitude = integer.unsigned_abs();
    let mut result = f.zero();
    let mut power = f.one();
    while magnitude != 0 {
        if magnitude & 1 != 0 {
            f.add(&mut result, &power);
        }
        magnitude >>= 1;
        if magnitude != 0 {
            power = f.addf(&power, &power);
        }
    }
    if integer < 0 {
        f.neg(&result)
    } else {
        result
    }
}
