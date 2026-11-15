// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
#[cfg(any(test, feature = "mdoc"))]
use crate::core::algebra::{Nat, SupportsNatConversions};
impl CoordinateMap {
    #[cfg(feature = "mdoc")]
    pub(crate) fn values(&self) -> &[Vec<Coordinate>] {
        &self.values
    }

    /// The values of the expanded claim's terms, in term order:
    /// `coordinate(value, c)` is coordinate `c` of a value, as a base-field
    /// element of E.
    #[cfg(any(test, feature = "mldsa"))]
    pub(crate) fn term_values<E>(
        &self,
        values: &[E],
        coordinate: impl Fn(&E, usize) -> E,
    ) -> Result<Vec<E>, String> {
        if values.len() != self.values.len() {
            return Err("coordinate value count".into());
        }
        if self.affine.is_some() {
            return Err("affine coordinates require encode_values".into());
        }
        Ok(self
            .values
            .iter()
            .zip(values)
            .flat_map(|(c, v)| c.iter().map(|x| coordinate(v, x.index)).collect::<Vec<_>>())
            .collect())
    }
    /// Pull native coordinates back to the committed unsigned integers and
    /// reject every value outside its group's range. Scales must be invertible
    /// in this field. `coordinate` returns a base coordinate embedded in F.
    #[cfg(any(test, feature = "mdoc"))]
    pub(crate) fn encode_values<const W: usize, F>(
        &self,
        values: &[F::E],
        coordinate: impl Fn(&F::E, usize) -> F::E,
        f: &F,
    ) -> Result<Vec<F::E>, String>
    where
        F: AlgebraicField + SupportsNatConversions<W>,
    {
        if values.len() != self.values.len() {
            return Err("coordinate value count".into());
        }
        let mut parameters = BTreeMap::new();
        let mut encoded = Vec::with_capacity(self.terms());
        for (slots, value) in self.values.iter().zip(values) {
            for slot in slots {
                let mut b = coordinate(value, slot.index);
                if let Some(encodings) = &self.affine {
                    let encoding = encodings[encoded.len()];
                    if encoding != AffineEncoding::IDENTITY {
                        let (offset, inverse) = match parameters.entry(encoding) {
                            Entry::Occupied(entry) => entry.into_mut(),
                            Entry::Vacant(entry) => {
                                let (scale, offset) = encoding.coefficients(f)?;
                                entry.insert((offset, f.invert(&scale)))
                            }
                        };
                        f.sub(&mut b, offset);
                        f.mul(&mut b, inverse);
                    }
                }
                if slot.group.width() < W * 64
                    && !fits_width::<W>(&f.to_nat(&b), slot.group.width())
                {
                    return Err("coordinate value exceeds its group width".into());
                }
                encoded.push(b);
            }
        }
        Ok(encoded)
    }
}
#[cfg(any(test, feature = "mdoc"))]
fn fits_width<const W: usize>(natural: &impl Nat<W>, width: usize) -> bool {
    let limbs = natural.to_limbs();
    let (whole, remaining) = (width / 64, width % 64);
    if whole >= W {
        return true;
    }
    if remaining == 0 {
        limbs[whole..].iter().all(|&limb| limb == 0)
    } else {
        limbs[whole] >> remaining == 0 && limbs[whole + 1..].iter().all(|&limb| limb == 0)
    }
}
