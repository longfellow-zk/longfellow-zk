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
        circuits::cbor::mdoc::{ParsedAttr, ParsedMdoc},
        proto::{
            config::K_ATTR_LEN_BITS,
            hash::constants::{
                K_COSE1_PREFIX_LEN, K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS, K_MSO_PREIMAGE_LEN,
            },
            layout,
            mso_attribute::constants::{
                K_ATTR_PREIMAGE_LEN, K_MAX_ATTR_CBOR_LEN, K_MAX_ATTR_SHA_BLOCKS,
            },
        },
        runtime::v2::{
            attribute::RequestedAttribute,
            error::MdocProverErrorCode,
            inputs::builder::{AssignmentBuilder, BinaryAssignmentBuilder},
        },
    },
    runtime::algebra::{field::RuntimeField, p256::P256Element},
};

pub(in crate::mdoc::runtime::v2) fn push_witness_hash<N: Nat<4>>(
    req_attrs: &[RequestedAttribute],
    parsed: &ParsedMdoc<N>,
) -> Result<Vec<bool>, MdocProverErrorCode> {
    let mut builder = BinaryAssignmentBuilder::new();
    // The leading private inputs follow the shared layout table, which the
    // runtime link reads; refuse to produce a witness that drifts from it.
    let at = |position: usize, range: &core::ops::Range<usize>, name: &str| {
        layout::check_at(position, range, name)
            .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)
    };

    // 1. issuer_sig_digest (256 bits)
    at(builder.len(), &layout::hash::ISSUER_DIGEST, "issuer digest")?;
    builder.push_nat256(&parsed.issuer_sig_digest);

    // 2. preimage (MSO preimage - bytes as bits) + preimage.len
    let mso_sha_in = crate::circuits::sha256msg::concrete::given(
        &parsed.cbor_mso,
        &crate::circuits::sha256::constants::INITIAL,
        K_MAX_SHA_BLOCKS,
    )
    .map_err(|_| MdocProverErrorCode::TaggedMsoTooBig)?;
    let requested = req_attrs.first().ok_or(MdocProverErrorCode::InvalidInput)?;
    let namespace = parsed
        .namespaces()
        .map_err(|_| MdocProverErrorCode::MsoDecodingFailure)?
        .into_iter()
        .find(|namespace| namespace.name == requested.namespace_id)
        .ok_or(MdocProverErrorCode::NamespacesMissing)?;
    // Scope once to the global namespace. Attribute lookup below stays name-only.
    let attributes: Vec<_> = parsed
        .attrs
        .iter()
        .filter(|attribute| {
            namespace
                .digest_range
                .contains(&attribute.mso_digest_offset_in_preimage)
        })
        .collect();
    let mso_sha_derived =
        crate::circuits::sha256msg::concrete::derived(&mso_sha_in, K_MAX_SHA_BLOCKS);
    let signed_bytes = &mso_sha_in.padded_preimage;
    let nblocks = mso_sha_in.nblocks;
    let preimage_arr: [u8; K_MSO_PREIMAGE_LEN] = signed_bytes.as_slice().try_into().unwrap();

    at(builder.len(), &layout::hash::MSO_PREIMAGE, "MSO preimage")?;
    for &b in &preimage_arr {
        builder.push_v8(b);
    }
    at(builder.len(), &layout::hash::MSO_LEN, "MSO length")?;
    builder.push_bits_len(parsed.cbor_mso.len() as u64, K_HASH_INDEX_BITS);

    // 3. nblocks (bytes as bits)
    at(builder.len(), &layout::hash::NBLOCKS, "block count")?;
    builder.push_v8(nblocks as u8);

    // 4. device_pkx and device_pky (256 bits)
    at(builder.len(), &layout::hash::DEVICE_X, "device x")?;
    builder.push_nat256(&parsed.device_pk.0);
    at(builder.len(), &layout::hash::DEVICE_Y, "device y")?;
    builder.push_nat256(&parsed.device_pk.1);
    let end = layout::hash::DEVICE_Y.end;
    at(builder.len(), &(end..end), "end of device y")?;

    // 5. doc_type / valid_from / valid_until / dev_key_info / value_digests offsets
    let preimage_base_offset = K_COSE1_PREFIX_LEN + 7;
    builder.push_bits_len(
        (preimage_base_offset + parsed.doc_type_offset_in_mso) as u64,
        K_HASH_INDEX_BITS,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.valid_from_offset_in_mso) as u64,
        K_HASH_INDEX_BITS,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.valid_until_offset_in_mso) as u64,
        K_HASH_INDEX_BITS,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.device_key_info_offset_in_mso) as u64,
        K_HASH_INDEX_BITS,
    );
    builder.push_bits_len(
        (preimage_base_offset + parsed.value_digests_offset_in_mso) as u64,
        K_HASH_INDEX_BITS,
    );
    builder.push_bits_len((preimage_base_offset + namespace.key_offset) as u64, K_HASH_INDEX_BITS);

    // 6. attribute_witnesses
    push_witness_attrs(req_attrs, &attributes, &mut builder)?;

    // 7. sha_witnesses (MSO preimage hashing)
    builder.push_sha256msg_derived(&mso_sha_derived);

    Ok(builder.into_inner())
}

fn push_witness_attrs(
    req_attrs: &[RequestedAttribute],
    attributes: &[&ParsedAttr],
    builder: &mut BinaryAssignmentBuilder,
) -> Result<(), MdocProverErrorCode> {
    for la in req_attrs {
        let pa = attributes
            .iter()
            .find(|attribute| attribute.name == la.id)
            .ok_or(MdocProverErrorCode::AttributeNotFound)?;
        if pa.cbor_value != la.cbor_value {
            return Err(MdocProverErrorCode::GeneralFailure);
        }
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
        builder.push_bits_len(mso_digest_offset_in_preimage as u64, K_HASH_INDEX_BITS);
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
) -> Result<Vec<F::E>, &'static str>
where
    F: crate::mdoc::circuits::MdocSigRuntimeField<E = P256Element>,
    Fn: RuntimeField<4> + crate::core::algebra::SupportsNatConversions<4, N = F::N>,
    C: Curve<4, F = F, N = F::N>,
    F::N: Nat<4>,
{
    let (issuer_sig_given, issuer_sig_derived) =
        crate::circuits::ecdsa2::concrete::try_witness::<4, F, Fn, C>(
            secp256r1,
            issuer_pk,
            &parsed.issuer_sig_digest,
            &parsed.issuer_sig_r,
            &parsed.issuer_sig_s,
            runtime_field,
            q256,
        )?;

    let (device_sig_given, device_sig_derived) =
        crate::circuits::ecdsa2::concrete::try_witness::<4, F, Fn, C>(
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
        )?;

    let mut builder = AssignmentBuilder::new(runtime_field);
    // The leading private inputs are the shared values of the layout table,
    // which the runtime link reads; refuse to drift from it.
    let at = |position: usize, range: &core::ops::Range<usize>| {
        layout::check_at(position, range, "signature input").map_err(|_| "signature input layout")
    };

    // 1. issuer_sig_digest
    at(builder.len(), &layout::sig::ISSUER_DIGEST)?;
    builder.push_nat_256_bits(&parsed.issuer_sig_digest);

    // 2. device_pk
    at(builder.len(), &layout::sig::DEVICE_X)?;
    builder.push_nat_256_bits(&parsed.device_pk.0);
    at(builder.len(), &layout::sig::DEVICE_Y)?;
    builder.push_nat_256_bits(&parsed.device_pk.1);
    at(builder.len(), &(layout::SHARED_BITS..layout::SHARED_BITS))?;

    // 3. issuer_sig_given
    builder.push_ecdsa_signature(&issuer_sig_given);

    // 4. device_sig_given
    builder.push_ecdsa_signature(&device_sig_given);

    // 5. issuer_sig_derived
    builder.push_ecdsa_derived(&issuer_sig_derived);

    // 6. device_sig_derived
    builder.push_ecdsa_derived(&device_sig_derived);

    Ok(builder.into_inner())
}
