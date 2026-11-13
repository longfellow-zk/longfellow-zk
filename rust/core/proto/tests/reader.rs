// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
#[test]
fn default_total_term_limit_matches_v2_limit() {
    let field = crate::compile::algebra::p256::P256Field::new();
    let reader = super::CircuitReader::new(&field, crate::core::proto::FieldID::P256);
    assert_eq!(
        reader.max_total_terms,
        crate::core::proto::v2::limits::MAX_TOTAL_TERMS
    );
}

#[test]
fn lfc3_rejects_zero_outputs_without_panicking() {
    use crate::core::proto::{serialize_uleb128_max4, FieldID};
    let field = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let mut bytes = b"LFC3DIR2".to_vec();
    for n in [FieldID::Gf2_128 as usize, 0, 1, 0, 0, 0, 0] {
        serialize_uleb128_max4(&mut bytes, n);
    }
    bytes.extend([0; 32]);
    assert!(super::CircuitReader::new(&field, FieldID::Gf2_128)
        .from_bytes(&bytes)
        .is_err());
}

struct Aliased(crate::runtime::algebra::gf2_128::Gf2_128Field);
impl crate::core::algebra::BareField for Aliased {
    type E = crate::runtime::algebra::gf2_128::Gf2_128;
}
impl crate::core::algebra::SerializableField for Aliased {
    fn is_binary(&self) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        16
    }
    fn to_bytes_into(&self, x: &Self::E, out: &mut [u8]) {
        self.0.to_bytes_into(x, out);
    }
    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        if bytes == [0xff; 16] {
            Ok(Self::E::from(0))
        } else {
            self.0.bytes_to_element(bytes)
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.0.serialized_mone()
    }
}

#[test]
fn lfc3_rejects_noncanonical_coefficients_even_with_a_valid_semantic_id() {
    use crate::core::{
        algebra::SerializableField,
        proto::{v2, v2::CircuitWriter, FieldID},
    };
    let field = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let raw = v2::RawCircuitBuilder {
        ninput: 1,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![crate::runtime::algebra::gf2_128::Gf2_128::from(0)],
        layers: vec![],
    }
    .build();
    let circuit = v2::Circuit::from_raw(&field, raw);
    let mut bytes = CircuitWriter::new(&field, FieldID::Gf2_128).to_bytes(&circuit);
    let mut remaining = &bytes[8..];
    for _ in 0..7 {
        crate::core::proto::read_uleb128_max4(&mut remaining).unwrap();
    }
    let offset = bytes.len() - remaining.len();
    bytes[offset..offset + field.serialized_size_bytes()].fill(0xff);
    assert!(super::CircuitReader::new(&Aliased(field), FieldID::Gf2_128)
        .from_bytes(&bytes)
        .is_err());
}
