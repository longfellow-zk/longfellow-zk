// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The native sextic MLDSA field as an extension of its prime field.
use super::{FiniteField, IdentityExtension, PackingExtension, PackingField};
use crate::{
    core::algebra::{AlgebraicField, BareField, SerializableField},
    runtime::algebra::fp24_ext6::{RuntimeElement, RuntimeFp24Ext6, Q},
};
#[derive(Clone, Copy, Debug, Default)]
pub struct Prime24;
impl BareField for Prime24 {
    type E = u32;
}
impl AlgebraicField for Prime24 {
    fn zero(&self) -> u32 {
        0
    }
    fn one(&self) -> u32 {
        1
    }
    fn add(&self, a: &mut u32, b: &u32) {
        *a = (*a + *b) % Q;
    }
    fn sub(&self, a: &mut u32, b: &u32) {
        *a = (*a + Q - *b) % Q;
    }
    fn mul(&self, a: &mut u32, b: &u32) {
        *a = (u64::from(*a) * u64::from(*b) % u64::from(Q)) as u32;
    }
    fn invert(&self, a: &u32) -> u32 {
        assert_ne!(*a, 0);
        super::pow_le(self, a, &(Q - 2).to_le_bytes())
    }
}
impl super::super::SupportsSampling for Prime24 {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, rng: R) -> u32 {
        crate::runtime::algebra::fp24_ext6::sample_base(rng)
    }
}
impl FiniteField for Prime24 {
    fn order_le(&self) -> Vec<u8> {
        Q.to_le_bytes()[..3].to_vec()
    }
    fn field_id(&self) -> Vec<u8> {
        b"prime/8380417/v1".to_vec()
    }
}
impl SerializableField for Prime24 {
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        3
    }
    fn to_bytes_into(&self, x: &u32, out: &mut [u8]) {
        out.copy_from_slice(&x.to_le_bytes()[..3]);
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<u32, String> {
        if b.len() != 3 {
            return Err("prime24 width".into());
        }
        let n = u32::from_le_bytes([b[0], b[1], b[2], 0]);
        if n >= Q {
            Err("prime24 encoding".into())
        } else {
            Ok(n)
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.to_bytes(&(Q - 1))
    }
}
impl PackingField for Prime24 {
    type Packing = IdentityExtension<Self>;
    fn packing_extension(&self) -> Self::Packing {
        IdentityExtension::new(*self)
    }
}
impl FiniteField for RuntimeFp24Ext6 {
    fn order_le(&self) -> Vec<u8> {
        let mut n = vec![1u8];
        for _ in 0..6 {
            let mut carry = 0u64;
            for digit in &mut n {
                carry += u64::from(*digit) * u64::from(Q);
                *digit = carry as u8;
                carry >>= 8;
            }
            while carry > 0 {
                n.push(carry as u8);
                carry >>= 8;
            }
        }
        n
    }
    fn field_id(&self) -> Vec<u8> {
        let mut id = b"prime24-sextic/v1/".to_vec();
        id.extend_from_slice(&crate::runtime::algebra::fp24_ext6::BETA.to_le_bytes());
        id
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct Prime24Extension;
impl PackingField for RuntimeFp24Ext6 {
    type Packing = Prime24Extension;
    fn packing_extension(&self) -> Self::Packing {
        Prime24Extension
    }
}
impl PackingExtension for Prime24Extension {
    fn extract_base(&self, _: &RuntimeFp24Ext6, x: &RuntimeElement) -> Result<u32, String> {
        if x.coefficients()[1..].iter().any(|&v| v != 0) {
            return Err("private input outside packing base field".into());
        }
        Ok(x.coefficients()[0])
    }
    type Base = Prime24;
    type Ambient = RuntimeFp24Ext6;
    fn base(&self) -> &Prime24 {
        &Prime24
    }
    fn degree(&self) -> usize {
        6
    }
    fn embedding_id(&self) -> Vec<u8> {
        b"prime24-to-sextic/constants/v1".to_vec()
    }
    fn embed(&self, f: &RuntimeFp24Ext6, x: &u32) -> RuntimeElement {
        f.from_coefficients([*x, 0, 0, 0, 0, 0])
    }
    fn native_basis(&self, f: &RuntimeFp24Ext6) -> Vec<RuntimeElement> {
        (0..6)
            .map(|j| {
                let mut c = [0; 6];
                c[j] = 1;
                f.from_coefficients(c)
            })
            .collect()
    }
    fn coordinates_into(&self, _: &RuntimeFp24Ext6, x: &RuntimeElement, out: &mut [u32]) {
        out.copy_from_slice(x.coefficients());
    }
}
