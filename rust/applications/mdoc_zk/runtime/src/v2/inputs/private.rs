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

//! Longfellow v2 private assignment encoding.

use crate::{
    core::algebra::{Curve, Nat},
    mdoc::{
        circuits::cbor::mdoc::ParsedMdoc,
        proto::{
            config::K_ATTR_LEN_BITS,
            hash::constants::{K_COSE1_PREFIX_LEN, K_MAX_SHA_BLOCKS, K_MSO_PREIMAGE_LEN},
            mso_attribute::constants::{
                K_ATTR_PREIMAGE_LEN, K_MAX_ATTR_CBOR_LEN, K_MAX_ATTR_SHA_BLOCKS,
            },
        },
        runtime::v2::{
            attribute::RequestedAttribute, error::MdocProverErrorCode,
            inputs::builder::AssignmentBuilder,
        },
    },
    runtime::algebra::{
        field::RuntimeField,
        gf2_128::{Gf2_128, Gf2_128Field},
        p256::P256Element,
    },
};

fn build_witness_hash<'a, N: Nat<4>>(
    mut builder: AssignmentBuilder<'a, Gf2_128Field>,
    req_attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<N>,
    mac_ap: &[[u128; 2]; 3],
) -> Result<AssignmentBuilder<'a, Gf2_128Field>, MdocProverErrorCode> {
    // 1. issuer_sig_digest (plucked V256)
    builder.push_nat256(&parsed.issuer_sig_digest);

    // 2. preimage (MSO preimage - plucked V8) + preimage.len
    let mso_sha_in = crate::circuits::sha256msg::concrete::given(
        &parsed.cbor_mso,
        &crate::circuits::sha256::constants::INITIAL,
        K_MAX_SHA_BLOCKS,
    )
    .map_err(|_| MdocProverErrorCode::TaggedMsoTooBig)?;
    let mso_sha_derived =
        crate::circuits::sha256msg::concrete::derived(&mso_sha_in, K_MAX_SHA_BLOCKS);
    let signed_bytes = &mso_sha_in.padded_preimage;
    let nblocks = mso_sha_in.nblocks;
    let preimage_arr: [u8; K_MSO_PREIMAGE_LEN] = signed_bytes.as_slice().try_into().unwrap();

    for &b in &preimage_arr {
        builder.push_v8(b);
    }
    builder.push_bits_len(parsed.cbor_mso.len() as u64, 16);

    // 3. nblocks (plucked V8)
    builder.push_v8(nblocks as u8);

    // 4. device_pkx and device_pky (plucked V256)
    builder.push_nat256(&parsed.device_pk.0);
    builder.push_nat256(&parsed.device_pk.1);

    // 5. doc_type / valid_from / valid_until / dev_key_info / value_digests offsets
    let preimage_base_offset = K_COSE1_PREFIX_LEN + 7;
    builder.push_bits_len(
        (preimage_base_offset + parsed.doc_type_offset_in_mso) as u64,
        16,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.valid_from_offset_in_mso) as u64,
        16,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.valid_until_offset_in_mso) as u64,
        16,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.device_key_info_offset_in_mso) as u64,
        16,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.value_digests_offset_in_mso) as u64,
        16,
    );

    // 6. attribute_witnesses
    push_witness_attrs(req_attrs, parsed, &mut builder)?;

    // 7. sha_witnesses (MSO preimage hashing)
    builder.push_sha256msg_derived(&mso_sha_derived);

    for pair in mac_ap {
        builder.push_mac_field(pair[0]);
        builder.push_mac_field(pair[1]);
    }

    Ok(builder)
}

pub(in crate::mdoc::runtime::v2) fn push_witness_hash<N: Nat<4>>(
    gf2: &Gf2_128Field,
    req_attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<N>,
    mac_ap: &[[u128; 2]; 3],
) -> Result<Vec<Gf2_128>, MdocProverErrorCode> {
    Ok(build_witness_hash(AssignmentBuilder::new(gf2), req_attrs, parsed, mac_ap)?.into_inner())
}
#[cfg(feature = "experimental")]
pub(in crate::mdoc::runtime::v2) fn push_witness_hash_boolean<N: Nat<4>>(
    gf2: &Gf2_128Field,
    req_attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<N>,
    mac_ap: &[[u128; 2]; 3],
) -> Result<Vec<Gf2_128>, MdocProverErrorCode> {
    Ok(build_witness_hash(
        AssignmentBuilder::new_boolean(gf2),
        req_attrs,
        parsed,
        mac_ap,
    )?
    .into_inner())
}

fn push_witness_attrs<N: Nat<4>>(
    req_attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<N>,
    builder: &mut AssignmentBuilder<Gf2_128Field>,
) -> Result<(), MdocProverErrorCode> {
    for la in req_attrs {
        let pa = parsed
            .get_attribute(&la.id)
            .ok_or(MdocProverErrorCode::AttributeNotFound)?;
        if pa.cbor_issuer_signed_item.len() > K_MAX_ATTR_CBOR_LEN {
            return Err(MdocProverErrorCode::AttributeTooLong);
        }
        let attr_sha_in = crate::circuits::sha256msg::concrete::given(
            &pa.cbor_issuer_signed_item,
            &crate::circuits::sha256::constants::INITIAL,
            K_MAX_ATTR_SHA_BLOCKS,
        )
        .map_err(|_| MdocProverErrorCode::AttributeTooLong)?;
        let attr_sha_derived =
            crate::circuits::sha256msg::concrete::derived(&attr_sha_in, K_MAX_ATTR_SHA_BLOCKS);
        let preimage_arr: [u8; K_ATTR_PREIMAGE_LEN] =
            attr_sha_in.padded_preimage.as_slice().try_into().unwrap();

        for &b in &preimage_arr {
            builder.push_v8(b);
        }
        builder.push_bits_len(pa.cbor_issuer_signed_item.len() as u64, K_ATTR_LEN_BITS);
        let preimage_base_offset = K_COSE1_PREFIX_LEN + 7;
        let mso_digest_offset_in_preimage = preimage_base_offset + pa.mso_digest_offset_in_preimage;
        builder.push_bits_len(mso_digest_offset_in_preimage as u64, 16);
        for &s in &pa.field_locator.slot_position {
            builder.push_bits_len(s as u64, K_ATTR_LEN_BITS);
        }
        for &l in &pa.field_locator.length {
            builder.push_bits_len(l as u64, K_ATTR_LEN_BITS);
        }
        let mut perm_val = pa.field_locator.permutation;
        for _ in 0..4 {
            let chunk = (perm_val & 3) as u64;
            builder.push_bits_len(chunk, 2);
            perm_val >>= 2;
        }
        builder.push_sha256msg_derived(&attr_sha_derived);
    }
    Ok(())
}

pub(in crate::mdoc::runtime::v2) fn push_witness_sig<F, Fn, C>(
    runtime_field: &F,
    q256: &Fn,
    secp256r1: &C,
    issuer_pk: &(F::E, F::E),
    parsed: &ParsedMdoc<F::N>,
    mac_ap: &[[u128; 2]; 3],
) -> Result<Vec<F::E>, String>
where
    F: crate::mdoc::circuits::MdocSigRuntimeField<E = P256Element>,
    Fn: RuntimeField<4> + crate::core::algebra::SupportsNatConversions<4, N = F::N>,
    C: Curve<4, F = F, N = F::N>,
    F::N: Nat<4>,
{
    let issuer_sig_given = crate::circuits::ecdsa2::concrete::given::<4, F, Fn, C>(
        secp256r1,
        &(issuer_pk.0, issuer_pk.1),
        &parsed.issuer_sig_digest,
        &parsed.issuer_sig_r,
        &parsed.issuer_sig_s,
        runtime_field,
        q256,
    );
    let issuer_sig_derived = crate::circuits::ecdsa2::concrete::derived(
        secp256r1,
        &(issuer_pk.0, issuer_pk.1),
        &parsed.issuer_sig_digest,
        &parsed.issuer_sig_r,
        &parsed.issuer_sig_s,
        runtime_field,
        q256,
    );

    let device_sig_given = crate::circuits::ecdsa2::concrete::given::<4, F, Fn, C>(
        secp256r1,
        &(
            runtime_field.reduce_nat(&parsed.device_pk.0),
            runtime_field.reduce_nat(&parsed.device_pk.1),
        ),
        &parsed.device_sig_digest,
        &parsed.device_sig_r,
        &parsed.device_sig_s,
        runtime_field,
        q256,
    );
    let device_sig_derived = crate::circuits::ecdsa2::concrete::derived(
        secp256r1,
        &(
            runtime_field.reduce_nat(&parsed.device_pk.0),
            runtime_field.reduce_nat(&parsed.device_pk.1),
        ),
        &parsed.device_sig_digest,
        &parsed.device_sig_r,
        &parsed.device_sig_s,
        runtime_field,
        q256,
    );

    let mut builder = AssignmentBuilder::new(runtime_field);

    // 1. issuer_sig_digest
    builder.push_nat_256_bits(&parsed.issuer_sig_digest);

    // 2. device_pk
    builder.push_nat_256_bits(&parsed.device_pk.0);
    builder.push_nat_256_bits(&parsed.device_pk.1);

    // 3. issuer_sig_given
    builder.push_ecdsa_given(&issuer_sig_given);

    // 4. device_sig_given
    builder.push_ecdsa_given(&device_sig_given);

    // 5. issuer_sig_derived
    builder.push_ecdsa_derived(&issuer_sig_derived);

    // 6. device_sig_derived
    builder.push_ecdsa_derived(&device_sig_derived);

    // 7. mac_ap
    for pair in mac_ap {
        builder.push_plucked_128(pair[0]);
        builder.push_plucked_128(pair[1]);
    }

    Ok(builder.into_inner())
}
