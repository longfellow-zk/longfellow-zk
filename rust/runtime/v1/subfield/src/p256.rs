// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::SubfieldV1;
use crate::runtime::algebra::p256::{P256Element, P256Field};

pub struct P256SubfieldV1<'a> {
    field: &'a P256Field,
}

impl<'a> P256SubfieldV1<'a> {
    #[must_use]
    pub fn new(field: &'a P256Field) -> Self {
        Self { field }
    }
}

impl SubfieldV1 for P256SubfieldV1<'_> {
    type E = P256Element;

    #[inline]
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(
            dst.len(),
            self.serialized_size_bytes(),
            "destination slice length mismatch: {} != {}",
            dst.len(),
            self.serialized_size_bytes()
        );
        crate::core::algebra::SerializableField::to_bytes_into(self.field, e, dst);
    }

    fn contains(&self, _e: &Self::E) -> bool {
        true
    }

    fn serialized_size_bytes(&self) -> usize {
        crate::core::algebra::SerializableField::serialized_size_bytes(self.field)
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        crate::core::algebra::SerializableField::bytes_to_element(self.field, bytes)
    }

    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, rng: R) -> Self::E {
        crate::runtime::algebra::field::SupportsSampling::sample(self.field, rng)
    }
}
