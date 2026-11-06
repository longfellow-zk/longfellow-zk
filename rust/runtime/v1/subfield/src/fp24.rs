// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::SubfieldV1;
use crate::runtime::algebra::{
    fp24_ext6::{
        sample_base, RuntimeElement, RuntimeFp24Ext6, BASE_SERIALIZED_SIZE, EXTENSION_DEGREE, Q,
    },
    range_interpolation::{CrtInterpolationPlan, InterpolationPlan},
};

pub struct RuntimeFp24SubfieldV1;

impl SubfieldV1 for RuntimeFp24SubfieldV1 {
    type E = RuntimeElement;

    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        assert_eq!(dst.len(), BASE_SERIALIZED_SIZE);
        assert!(self.contains(e), "element is not in the Fp24 base field");
        dst.copy_from_slice(&e.coefficients()[0].to_le_bytes()[..BASE_SERIALIZED_SIZE]);
    }

    fn contains(&self, e: &Self::E) -> bool {
        e.coefficients()[1..]
            .iter()
            .all(|&coefficient| coefficient == 0)
    }

    fn serialized_size_bytes(&self) -> usize {
        BASE_SERIALIZED_SIZE
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        if bytes.len() != BASE_SERIALIZED_SIZE {
            return Err("invalid Fp24 base-field element size".to_owned());
        }
        let value = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]);
        if value >= Q {
            return Err("non-canonical Fp24 base-field element".to_owned());
        }
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = value;
        Ok(RuntimeElement::new(coefficients))
    }

    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
        let mut coefficients = [0; EXTENSION_DEGREE];
        coefficients[0] = sample_base(&mut rng);
        RuntimeElement::new(coefficients)
    }
}

impl super::InterpolationPlanV1<3, RuntimeFp24Ext6> for CrtInterpolationPlan {
    fn apply_subfield_v1<SF: SubfieldV1<E = RuntimeElement>>(
        &self,
        source: &[RuntimeElement],
        sf: &SF,
    ) -> Vec<RuntimeElement> {
        if sf.serialized_size_bytes() != 3 {
            return self.apply(source);
        }
        assert!(
            source
                .iter()
                .all(|x| x.coefficients()[1..].iter().all(|&c| c == 0)),
            "invalid base-subfield interpolation hint"
        );
        self.apply_components(source, 1)
    }
}
