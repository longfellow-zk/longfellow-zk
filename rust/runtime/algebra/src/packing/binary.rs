// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The existing polynomial GF(2^128) representation over GF(2).
use super::{FiniteField, PackingExtension, PackingField};
use crate::{
    core::algebra::{AlgebraicField, BareField, SerializableField},
    runtime::algebra::gf2_128::{Gf2_128, Gf2_128Field},
};

#[derive(Clone, Copy, Debug, Default)]
pub struct Gf2;
impl BareField for Gf2 {
    type E = bool;
}
impl AlgebraicField for Gf2 {
    fn zero(&self) -> bool {
        false
    }
    fn one(&self) -> bool {
        true
    }
    fn add(&self, a: &mut bool, b: &bool) {
        *a ^= *b;
    }
    fn sub(&self, a: &mut bool, b: &bool) {
        *a ^= *b;
    }
    fn mul(&self, a: &mut bool, b: &bool) {
        *a &= *b;
    }
    fn invert(&self, a: &bool) -> bool {
        assert!(*a);
        true
    }
}
impl super::super::SupportsSampling for Gf2 {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> bool {
        let bytes = rng(1);
        assert_eq!(
            bytes.len(),
            1,
            "sampling callback returned an unexpected number of bytes"
        );
        bytes[0] & 1 != 0
    }
}
impl FiniteField for Gf2 {
    fn order_le(&self) -> Vec<u8> {
        vec![2]
    }
    fn field_id(&self) -> Vec<u8> {
        b"GF2/v1".to_vec()
    }
}
impl SerializableField for Gf2 {
    fn is_binary(&self) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        1
    }
    fn to_bytes_into(&self, x: &bool, out: &mut [u8]) {
        out[0] = u8::from(*x);
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<bool, String> {
        match b {
            [0] => Ok(false),
            [1] => Ok(true),
            _ => Err("noncanonical GF2".into()),
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        vec![1]
    }
}
impl PackingField for Gf2 {
    type Packing = super::IdentityExtension<Self>;
    fn packing_extension(&self) -> Self::Packing {
        super::IdentityExtension::new(*self)
    }
}
impl FiniteField for Gf2_128Field {
    fn order_le(&self) -> Vec<u8> {
        let mut n = vec![0; 17];
        n[16] = 1;
        n
    }
    fn field_id(&self) -> Vec<u8> {
        b"GF2[x]/(x^128+x^7+x^2+x+1)/polynomial/v1".to_vec()
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct Binary128Extension;
impl PackingField for Gf2_128Field {
    type Packing = Binary128Extension;
    fn packing_extension(&self) -> Binary128Extension {
        Binary128Extension
    }
}
impl PackingExtension for Binary128Extension {
    fn extract_base(&self, _: &Gf2_128Field, x: &Gf2_128) -> Result<bool, String> {
        match x.to_u128() {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err("private input outside packing base field".into()),
        }
    }
    fn native_dual_basis(&self, f: &Gf2_128Field) -> Option<Vec<Gf2_128>> {
        let b = super::binary128::PolynomialBasis128::new(f);
        Some((0..128).map(|j| b.dual(j)).collect())
    }
    fn native_coefficients(
        &self,
        f: &Gf2_128Field,
        row: &[Gf2_128],
        dual: &[Gf2_128],
    ) -> Option<Vec<Gf2_128>> {
        Some(
            super::binary128::dual_coordinate_numerators(row)
                .into_iter()
                .map(|n| f.mulf(&dual[127], &n))
                .collect(),
        )
    }
    type Base = Gf2;
    type Ambient = Gf2_128Field;
    fn binary128_profile(&self) -> bool {
        true
    }
    fn base(&self) -> &Gf2 {
        &Gf2
    }
    fn degree(&self) -> usize {
        128
    }
    fn embedding_id(&self) -> Vec<u8> {
        b"GF2-to-GF128/polynomial/v1".to_vec()
    }
    fn embed(&self, _: &Gf2_128Field, x: &bool) -> Gf2_128 {
        Gf2_128::from(u128::from(*x))
    }
    fn native_basis(&self, _: &Gf2_128Field) -> Vec<Gf2_128> {
        (0..128).map(|j| Gf2_128::from(1u128 << j)).collect()
    }
    fn coordinates_into(&self, _: &Gf2_128Field, x: &Gf2_128, out: &mut [bool]) {
        assert_eq!(out.len(), 128);
        for (j, b) in out.iter_mut().enumerate() {
            *b = x.bit(j);
        }
    }
    fn relative_frobenius(&self, f: &Gf2_128Field, x: &Gf2_128) -> Gf2_128 {
        f.mulf(x, x)
    }
}

/// GF(256) uses powers of a deterministically selected primitive element.
/// Its element type is distinct from GF128's and its encoding is one byte.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Gf256Element(Gf2_128);
pub struct Gf256 {
    field: Gf2_128Field,
    basis: [Gf2_128; 8],
    digits: [u128; 8],
}
impl Gf256 {
    pub fn new() -> Self {
        let field = Gf2_128Field::new();
        let generator = (2u128..)
            .map(|candidate| {
                super::pow_le(
                    &field,
                    &Gf2_128::from(candidate),
                    &(u128::MAX / 255).to_le_bytes(),
                )
            })
            .find(|g| {
                [3u8, 5, 17]
                    .iter()
                    .all(|prime| super::pow_le(&field, g, &[255 / prime]) != field.one())
            })
            .expect("primitive GF256 element");
        let mut power = field.one();
        let basis = std::array::from_fn(|_| {
            let value = power;
            power = field.mulf(&power, &generator);
            value
        });
        // Extend the eight basis vectors to a full binary basis to obtain
        // fixed parity masks for canonical serialization.
        let mut independent = Vec::new();
        let mut pivots = [0u128; 128];
        for v in basis
            .iter()
            .copied()
            .chain((0..128).map(|j| Gf2_128::from(1u128 << j)))
        {
            let mut x = v.to_u128();
            for j in (0..128).rev() {
                if x >> j & 1 != 0 {
                    if pivots[j] == 0 {
                        pivots[j] = x;
                        independent.push(v);
                        break;
                    }
                    x ^= pivots[j];
                }
            }
        }
        let inverse = binary_inverse(&independent);
        let digits = std::array::from_fn(|i| inverse[i]);
        Self {
            field,
            basis,
            digits,
        }
    }
    pub fn element(&self, byte: u8) -> Gf256Element {
        let mut word = 0;
        for i in 0..8 {
            word ^= self.basis[i].to_u128() & 0u128.wrapping_sub(u128::from(byte >> i & 1));
        }
        Gf256Element(Gf2_128::from(word))
    }
    pub fn byte(&self, x: &Gf256Element) -> u8 {
        self.digits.iter().enumerate().fold(0, |n, (i, mask)| {
            n | ((((x.0.to_u128() & mask).count_ones() & 1) as u8) << i)
        })
    }
}
impl Default for Gf256 {
    fn default() -> Self {
        Self::new()
    }
}
impl BareField for Gf256 {
    type E = Gf256Element;
}
impl AlgebraicField for Gf256 {
    fn zero(&self) -> Self::E {
        Gf256Element(self.field.zero())
    }
    fn one(&self) -> Self::E {
        Gf256Element(self.field.one())
    }
    fn add(&self, a: &mut Self::E, b: &Self::E) {
        self.field.add(&mut a.0, &b.0);
    }
    fn sub(&self, a: &mut Self::E, b: &Self::E) {
        self.field.sub(&mut a.0, &b.0);
    }
    fn mul(&self, a: &mut Self::E, b: &Self::E) {
        self.field.mul(&mut a.0, &b.0);
    }
    fn invert(&self, a: &Self::E) -> Self::E {
        Gf256Element(self.field.invert(&a.0))
    }
}
impl super::super::SupportsSampling for Gf256 {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
        let bytes = rng(1);
        assert_eq!(
            bytes.len(),
            1,
            "sampling callback returned an unexpected number of bytes"
        );
        self.element(bytes[0])
    }
}
impl FiniteField for Gf256 {
    fn order_le(&self) -> Vec<u8> {
        vec![0, 1]
    }
    fn field_id(&self) -> Vec<u8> {
        {
            let mut id = b"GF256/primitive-powers/v1/".to_vec();
            id.extend_from_slice(&self.basis[1].to_u128().to_le_bytes());
            id
        }
    }
}
impl SerializableField for Gf256 {
    fn is_binary(&self) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        1
    }
    fn to_bytes_into(&self, x: &Self::E, b: &mut [u8]) {
        b[0] = self.byte(x);
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<Self::E, String> {
        match b {
            [v] => Ok(self.element(*v)),
            _ => Err("GF256 encoding width".into()),
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.to_bytes(&self.one())
    }
}
impl PackingField for Gf256 {
    type Packing = super::IdentityExtension<Self>;
    fn packing_extension(&self) -> Self::Packing {
        super::IdentityExtension::new(Self::new())
    }
}

/// A second adapter for the *same* ambient GF128 field, now over GF256.
pub struct Binary128Over256 {
    base: Gf256,
    inverse: [u128; 128],
}
impl Binary128Over256 {
    pub fn new() -> Self {
        let base = Gf256::new();
        let f = &base.field;
        let tensor = (0..16)
            .flat_map(|j| {
                base.basis
                    .iter()
                    .map(move |b| f.mulf(b, &Gf2_128::from(1u128 << j)))
            })
            .collect::<Vec<_>>();
        let inverse = binary_inverse(&tensor);
        Self { base, inverse }
    }
}
impl Default for Binary128Over256 {
    fn default() -> Self {
        Self::new()
    }
}
impl PackingExtension for Binary128Over256 {
    type Base = Gf256;
    type Ambient = Gf2_128Field;
    fn base(&self) -> &Gf256 {
        &self.base
    }
    fn degree(&self) -> usize {
        16
    }
    fn embedding_id(&self) -> Vec<u8> {
        b"GF256-to-GF128/primitive-powers/v1".to_vec()
    }
    fn embed(&self, _: &Gf2_128Field, x: &Gf256Element) -> Gf2_128 {
        x.0
    }
    fn native_basis(&self, _: &Gf2_128Field) -> Vec<Gf2_128> {
        (0..16).map(|j| Gf2_128::from(1u128 << j)).collect()
    }
    fn coordinates_into(&self, _: &Gf2_128Field, x: &Gf2_128, out: &mut [Gf256Element]) {
        assert_eq!(out.len(), 16);
        for (i, v) in out.iter_mut().enumerate() {
            let byte = (0..8).fold(0u8, |b, j| {
                b | ((((x.to_u128() & self.inverse[8 * i + j]).count_ones() & 1) as u8) << j)
            });
            *v = self.base.element(byte);
        }
    }
    fn relative_frobenius(&self, f: &Gf2_128Field, x: &Gf2_128) -> Gf2_128 {
        let mut v = *x;
        for _ in 0..8 {
            v = f.mulf(&v, &v);
        }
        v
    }
}
fn binary_inverse(basis: &[Gf2_128]) -> [u128; 128] {
    assert_eq!(basis.len(), 128);
    let mut rows = std::array::from_fn::<_, 128, _>(|i| {
        basis
            .iter()
            .enumerate()
            .fold(0, |r, (j, v)| r | (u128::from(v.bit(i)) << j))
    });
    let mut inverse = std::array::from_fn::<_, 128, _>(|j| 1u128 << j);
    for j in 0..128 {
        let pivot = (j..128)
            .find(|&i| rows[i] >> j & 1 != 0)
            .expect("binary extension basis");
        rows.swap(j, pivot);
        inverse.swap(j, pivot);
        for i in 0..128 {
            if i != j && rows[i] >> j & 1 != 0 {
                rows[i] ^= rows[j];
                inverse[i] ^= inverse[j];
            }
        }
    }
    inverse
}
