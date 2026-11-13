// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::{AlgebraicField, BareField, SupportsNatConversions, SupportsU64Conversions},
    runtime::algebra::{
        fp_generic::FpGenericField, p256::P256Field,
        range_interpolation::ScalarInterpolatorFactory, LIMBS_PER_U64,
    },
};

fn config() -> PolygeroConfig {
    PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    }
}

#[test]
fn participant_uses_the_domains_runtime_modulus() {
    type Prime = FpGenericField<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }>;
    let f17 = Prime::new_generic([17]);
    let f19 = Prime::new_generic([19]);
    let d17 = ScalarInterpolatorFactory::new(&f17, 16);
    let d19 = ScalarInterpolatorFactory::new(&f19, 16);
    let config = PolygeroConfig {
        k: 2,
        s: 1,
        n: 8,
        t: 1,
    };
    let p17 = PolygeroParam::try_new(3, config, &d17).unwrap();
    let p19 = PolygeroParam::try_new(3, config, &d19).unwrap();
    let participant17 = Participant::new(p17.clone(), &d17).unwrap();
    let participant19 = Participant::new(p19, &d19).unwrap();

    // These fields have the same Rust type but different runtime arithmetic.
    // The constructor has no independent field argument to get out of sync.
    assert!(std::ptr::eq(participant17.f, &f17));
    assert!(std::ptr::eq(participant19.f, &f19));
    assert_eq!(participant17.f.u64_to_element(17), participant17.f.zero());
    assert_ne!(participant19.f.u64_to_element(17), participant19.f.zero());
    assert!(Participant::new(p17, &d19).is_err());
}

#[test]
fn attaching_a_domain_rechecks_capacity_even_when_its_identity_matches() {
    let f = P256Field::new();
    let large = ScalarInterpolatorFactory::new(&f, 128);
    let small = ScalarInterpolatorFactory::new(&f, 16);
    assert_eq!(large.domain_id(), small.domain_id());
    assert!(config().can_interpolate(&large));
    assert!(!config().can_interpolate(&small));
    let param = PolygeroParam::try_new(17, config(), &large).unwrap();
    assert!(Participant::new(param.clone(), &large).is_ok());
    assert!(Participant::new(param, &small).is_err());
}

/// Keep real P256 arithmetic while varying only its advertised encoding width.
/// Serialization is deliberately unreachable: invalid widths must be rejected
/// when attaching the participant, before any proof or transcript is written.
struct EncodingWidth {
    field: P256Field,
    bytes: usize,
}
impl BareField for EncodingWidth {
    type E = <P256Field as BareField>::E;
}
impl AlgebraicField for EncodingWidth {
    fn zero(&self) -> Self::E {
        self.field.zero()
    }
    fn one(&self) -> Self::E {
        self.field.one()
    }
    fn add(&self, a: &mut Self::E, b: &Self::E) {
        self.field.add(a, b);
    }
    fn sub(&self, a: &mut Self::E, b: &Self::E) {
        self.field.sub(a, b);
    }
    fn mul(&self, a: &mut Self::E, b: &Self::E) {
        self.field.mul(a, b);
    }
    fn invert(&self, a: &Self::E) -> Self::E {
        self.field.invert(a)
    }
}
impl RuntimeField<4> for EncodingWidth {
    type Accum = <P256Field as RuntimeField<4>>::Accum;
    fn zero_accum(&self) -> Self::Accum {
        self.field.zero_accum()
    }
    fn mac(&self, a: &mut Self::Accum, x: &Self::E, y: &Self::E) {
        self.field.mac(a, x, y);
    }
    fn accum_reduce(&self, a: &Self::Accum) -> Self::E {
        self.field.accum_reduce(a)
    }
}
impl SupportsSampling for EncodingWidth {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, rng: R) -> Self::E {
        self.field.sample(rng)
    }
}
impl SerializableField for EncodingWidth {
    fn field_id(&self) -> crate::core::algebra::FieldID {
        crate::core::algebra::FieldID::None
    }
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        self.bytes
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.field.serialized_mone()
    }
    fn to_bytes_into(&self, _: &Self::E, _: &mut [u8]) {
        unreachable!("constructor serialized a field element")
    }
    fn bytes_to_element(&self, _: &[u8]) -> Result<Self::E, String> {
        unreachable!("constructor decoded a field element")
    }
}
impl SupportsNatConversions<4> for EncodingWidth {
    type N = <P256Field as SupportsNatConversions<4>>::N;
    fn reduce_nat(&self, n: &Self::N) -> Self::E {
        self.field.reduce_nat(n)
    }
    fn to_nat(&self, x: &Self::E) -> Self::N {
        self.field.to_nat(x)
    }
}
impl SupportsU64Conversions for EncodingWidth {
    fn u64_to_element(&self, n: u64) -> Self::E {
        self.field.u64_to_element(n)
    }
}

#[test]
fn attaching_a_field_rejects_unsupported_transcript_encoding_widths() {
    let limit = crate::runtime::v2::transcript::MAX_FIELD_BYTES;
    for bytes in [0, 32, limit, limit + 1, usize::MAX] {
        let f = EncodingWidth {
            field: P256Field::new(),
            bytes,
        };
        let d = ScalarInterpolatorFactory::new(&f, 128);
        let param = PolygeroParam::try_new(17, config(), &d).unwrap();
        assert_eq!(
            Participant::new(param, &d).is_ok(),
            matches!(bytes, 32) || bytes == limit
        );
    }
}
