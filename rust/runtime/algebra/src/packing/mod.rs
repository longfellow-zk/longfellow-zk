// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Finite extensions and explicitly owned packing parameters. These interfaces
//! describe an extension F/K, independently of legacy V1 serialization hints.

use crate::core::algebra::{AlgebraicField, SerializableField};

pub mod binary;
pub mod binary128;
#[cfg(feature = "experimental")]
pub mod prime24;

/// Cardinalities and field identities are byte strings, without a machine-word
/// restriction. Integers use canonical unsigned little-endian encoding.
pub trait FiniteField: super::SupportsSampling {
    fn order_le(&self) -> Vec<u8>;
    /// A canonical identity of the field representation (including its modulus).
    fn field_id(&self) -> Vec<u8>;
}

/// The default extension is an ordinary associated type selected explicitly by
/// each field implementation. Other adapters for the same field remain usable.
pub trait PackingField: FiniteField + Sized {
    type Packing: PackingExtension<Ambient = Self>;
    fn packing_extension(&self) -> Self::Packing;
}

/// Trusted arithmetic adapter for a particular embedding K -> F. Implementors
/// must supply a field embedding and coordinates in a K-basis of length degree.
/// Coordinates have type Base::E; they need not be Boolean.
pub trait PackingExtension {
    type Base: FiniteField;
    type Ambient: FiniteField;
    fn native_dual_basis(&self, _: &Self::Ambient) -> Option<Vec<AmbientElement<Self>>>
    where Self: Sized {
        None
    }
    fn native_coefficients(
        &self,
        _: &Self::Ambient,
        _: &[AmbientElement<Self>],
        _: &[AmbientElement<Self>],
    ) -> Option<Vec<AmbientElement<Self>>>
    where
        Self: Sized,
    {
        None
    }
    /// Invert the embedding on its image; reject ambient values outside K.
    fn extract_base(
        &self,
        f: &Self::Ambient,
        x: &AmbientElement<Self>,
    ) -> Result<BaseElement<Self>, String>
    where
        Self: Sized,
    {
        let b = self.base();
        let mut unit = vec![b.zero(); self.degree()];
        let mut coordinates = unit.clone();
        self.coordinates_into(f, &f.one(), &mut unit);
        self.coordinates_into(f, x, &mut coordinates);
        let i = unit
            .iter()
            .position(|v| *v != b.zero())
            .ok_or("invalid field embedding")?;
        let value = b.mulf(&coordinates[i], &b.invert(&unit[i]));
        if self.embed(f, &value) != *x {
            return Err("private input outside packing base field".into());
        }
        Ok(value)
    }
    fn base(&self) -> &Self::Base;
    /// Opt-in compatibility for the shipped polynomial GF128/GF2 profile.
    fn binary128_profile(&self) -> bool {
        false
    }
    fn degree(&self) -> usize;
    fn embedding_id(&self) -> Vec<u8>;
    fn embed(
        &self,
        f: &Self::Ambient,
        x: &<Self::Base as crate::core::algebra::BareField>::E,
    ) -> <Self::Ambient as crate::core::algebra::BareField>::E;
    fn native_basis(
        &self,
        f: &Self::Ambient,
    ) -> Vec<<Self::Ambient as crate::core::algebra::BareField>::E>;
    fn coordinates_into(
        &self,
        f: &Self::Ambient,
        x: &<Self::Ambient as crate::core::algebra::BareField>::E,
        out: &mut [<Self::Base as crate::core::algebra::BareField>::E],
    );
    fn relative_frobenius(
        &self,
        f: &Self::Ambient,
        x: &<Self::Ambient as crate::core::algebra::BareField>::E,
    ) -> <Self::Ambient as crate::core::algebra::BareField>::E {
        pow_le(f, x, &self.base().order_le())
    }
}

pub type AmbientElement<X> =
    <<X as PackingExtension>::Ambient as crate::core::algebra::BareField>::E;
pub type BaseElement<X> = <<X as PackingExtension>::Base as crate::core::algebra::BareField>::E;

/// Exponentiation by an arbitrary-size nonnegative public exponent.
pub fn pow_le<F: AlgebraicField>(f: &F, x: &F::E, exponent: &[u8]) -> F::E {
    let mut value = f.one();
    for byte in exponent.iter().rev() {
        for bit in (0..8).rev() {
            value = f.mulf(&value, &value);
            if (byte >> bit) & 1 != 0 {
                f.mul(&mut value, x);
            }
        }
    }
    value
}

/// Degree-one adapter. It owns its base arithmetic, and has no protocol state.
pub struct IdentityExtension<F> {
    base: F,
}
impl<F> IdentityExtension<F> {
    pub fn new(base: F) -> Self {
        Self { base }
    }
}
impl<F: FiniteField> PackingExtension for IdentityExtension<F> {
    fn extract_base(&self, _: &F, x: &F::E) -> Result<F::E, String> {
        Ok(x.clone())
    }
    type Base = F;
    type Ambient = F;
    fn base(&self) -> &F {
        &self.base
    }
    fn degree(&self) -> usize {
        1
    }
    fn embedding_id(&self) -> Vec<u8> {
        b"identity/v1".to_vec()
    }
    fn embed(&self, _: &F, x: &F::E) -> F::E {
        x.clone()
    }
    fn native_basis(&self, f: &F) -> Vec<F::E> {
        vec![f.one()]
    }
    fn coordinates_into(&self, _: &F, x: &F::E, out: &mut [F::E]) {
        assert_eq!(out.len(), 1);
        out[0] = x.clone();
    }
    fn relative_frobenius(&self, _: &F, x: &F::E) -> F::E {
        x.clone()
    }
}

/// Owned initialization shared by all invocations using one chosen basis.
/// The distinguished coordinate must complement K: the first coordinate of
/// one is nonzero. This includes singleton bases beta != 1.
pub struct PackingParameters<X: PackingExtension> {
    field: X::Ambient,
    extension: X,
    basis: Vec<AmbientElement<X>>,
    dual: Vec<AmbientElement<X>>,
    inverse: Option<Vec<Vec<BaseElement<X>>>>,
}
impl<X: PackingExtension> PackingParameters<X> {
    pub fn new(field: X::Ambient, extension: X) -> Result<Self, String> {
        let basis = extension.native_basis(&field);
        Self::with_basis(field, extension, basis)
    }
    pub fn with_basis(
        field: X::Ambient,
        extension: X,
        basis: Vec<AmbientElement<X>>,
    ) -> Result<Self, String> {
        let m = extension.degree();
        if m == 0 || basis.len() != m {
            return Err("packing basis length".into());
        }
        let native = basis == extension.native_basis(&field);
        let base = extension.base();
        let mut coordinates = vec![base.zero(); m];
        let mut matrix = vec![vec![base.zero(); m]; m];
        for (j, beta) in basis.iter().enumerate() {
            extension.coordinates_into(&field, beta, &mut coordinates);
            for i in 0..m {
                matrix[i][j] = coordinates[i].clone();
            }
        }
        let inverse = invert_matrix(base, matrix)?;
        // The fixed mask relation t_0=sum_(j>0) beta_j*t_j hides every
        // trace-zero coordinate only when {1,beta_1,...} is a basis.
        extension.coordinates_into(&field, &field.one(), &mut coordinates);
        let unit_first = inverse[0]
            .iter()
            .zip(&coordinates)
            .fold(base.zero(), |a, (k, x)| base.addf(&a, &base.mulf(k, x)));
        if base.is_zero(&unit_first) {
            return Err("packing basis must complement K at coordinate zero".into());
        }
        let mut parameters = Self {
            field,
            extension,
            basis,
            inverse: if native { None } else { Some(inverse) },
            dual: Vec::new(),
        };
        if native {
            if let Some(dual) = parameters.extension.native_dual_basis(&parameters.field) {
                if dual.len() != m {
                    return Err("native trace-dual basis length".into());
                }
                parameters.dual = dual;
                return Ok(parameters);
            }
        }
        let gram = parameters
            .basis
            .iter()
            .map(|a| {
                parameters
                    .basis
                    .iter()
                    .map(|b| parameters.trace(&parameters.field.mulf(a, b)))
                    .collect()
            })
            .collect();
        let gram_inverse = invert_matrix(&parameters.field, gram)?;
        parameters.dual = (0..m)
            .map(|j| {
                let mut value = parameters.field.zero();
                for (k, beta) in parameters.basis.iter().enumerate() {
                    parameters.field.add(
                        &mut value,
                        &parameters.field.mulf(beta, &gram_inverse[k][j]),
                    );
                }
                value
            })
            .collect();
        Ok(parameters)
    }
    pub fn field(&self) -> &X::Ambient {
        &self.field
    }
    pub fn extension(&self) -> &X {
        &self.extension
    }
    pub fn degree(&self) -> usize {
        self.basis.len()
    }
    pub fn basis(&self) -> &[AmbientElement<X>] {
        &self.basis
    }
    pub fn dual(&self) -> &[AmbientElement<X>] {
        &self.dual
    }
    pub fn frobenius(&self, x: &AmbientElement<X>) -> AmbientElement<X> {
        self.extension.relative_frobenius(&self.field, x)
    }
    /// Trace represented in F, without dividing by the extension degree.
    pub fn trace(&self, x: &AmbientElement<X>) -> AmbientElement<X> {
        let mut image = x.clone();
        let mut sum = self.field.zero();
        for _ in 0..self.degree() {
            self.field.add(&mut sum, &image);
            image = self.frobenius(&image);
        }
        sum
    }
    pub fn coordinates_into(&self, x: &AmbientElement<X>, out: &mut [BaseElement<X>]) {
        let m = self.degree();
        assert_eq!(out.len(), m);
        if self.inverse.is_none() {
            self.extension.coordinates_into(&self.field, x, out);
            return;
        }
        let b = self.extension.base();
        let mut native = vec![b.zero(); m];
        self.extension.coordinates_into(&self.field, x, &mut native);
        for (i, row) in self.inverse.as_ref().unwrap().iter().enumerate() {
            out[i] = b.zero();
            for (k, c) in row.iter().zip(&native) {
                b.add(&mut out[i], &b.mulf(k, c));
            }
        }
    }
    /// Partial blocks have zero padding on packing. Claims need not constrain
    /// unused coordinates of their final committed word.
    pub fn pack(&self, values: &[BaseElement<X>]) -> Result<Vec<AmbientElement<X>>, String> {
        values
            .chunks(self.degree())
            .map(|block| {
                let mut word = self.field.zero();
                for (beta, x) in self.basis.iter().zip(block) {
                    self.field.add(
                        &mut word,
                        &self.field.mulf(beta, &self.extension.embed(&self.field, x)),
                    );
                }
                Ok(word)
            })
            .collect()
    }
    pub fn unpack(
        &self,
        words: &[AmbientElement<X>],
        len: usize,
    ) -> Result<Vec<BaseElement<X>>, String> {
        if words.len() != len.div_ceil(self.degree()) {
            return Err("packing word count".into());
        }
        let mut result = Vec::with_capacity(len);
        let mut coordinates = vec![self.extension.base().zero(); self.degree()];
        for word in words {
            self.coordinates_into(word, &mut coordinates);
            result.extend(coordinates.iter().take(len - result.len()).cloned());
        }
        Ok(result)
    }
    pub fn native_coefficients(&self, row: &[AmbientElement<X>]) -> Option<Vec<AmbientElement<X>>> {
        if self.inverse.is_none() {
            self.extension
                .native_coefficients(&self.field, row, &self.dual)
                .inspect(|coefficients| {
                    assert_eq!(
                        coefficients.len(),
                        self.degree(),
                        "native coefficient shape"
                    );
                })
        } else {
            None
        }
    }
    pub fn binary128_profile(&self) -> bool {
        self.extension.binary128_profile() && self.inverse.is_none()
    }
    pub fn descriptor(&self) -> Vec<u8>
    where X::Ambient: SerializableField {
        let mut bytes = b"longfellow/packing-extension/v1".to_vec();
        for part in [
            self.field.field_id(),
            self.field.order_le(),
            self.extension.base().field_id(),
            self.extension.base().order_le(),
            self.extension.embedding_id(),
            (self.degree() as u64).to_le_bytes().to_vec(),
        ] {
            bytes.extend_from_slice(&(part.len() as u64).to_le_bytes());
            bytes.extend_from_slice(&part);
        }
        for beta in &self.basis {
            bytes.extend_from_slice(&self.field.to_bytes(beta));
        }
        bytes
    }
}

fn invert_matrix<F: AlgebraicField>(
    f: &F,
    mut a: Vec<Vec<F::E>>,
) -> Result<Vec<Vec<F::E>>, String> {
    let m = a.len();
    let mut inverse = vec![vec![f.zero(); m]; m];
    for (i, row) in inverse.iter_mut().enumerate() {
        row[i] = f.one();
    }
    for j in 0..m {
        let pivot = (j..m)
            .find(|&i| !f.is_zero(&a[i][j]))
            .ok_or("singular packing basis or trace pairing")?;
        a.swap(j, pivot);
        inverse.swap(j, pivot);
        let scale = f.invert(&a[j][j]);
        for k in 0..m {
            f.mul(&mut a[j][k], &scale);
            f.mul(&mut inverse[j][k], &scale);
        }
        for i in 0..m {
            if i == j {
                continue;
            }
            let factor = a[i][j].clone();
            if f.is_zero(&factor) {
                continue;
            }
            for k in 0..m {
                let row_shift = f.mulf(&factor, &a[j][k]);
                f.sub(&mut a[i][k], &row_shift);
                let inverse_shift = f.mulf(&factor, &inverse[j][k]);
                f.sub(&mut inverse[i][k], &inverse_shift);
            }
        }
    }
    Ok(inverse)
}
