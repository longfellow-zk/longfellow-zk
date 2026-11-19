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

use sha2::{Digest, Sha256};

use crate::{
    circuits::{
        ecdsa2::{try_witness, Derived, Given},
        sha256msg::{given_and_derived, Derived as ShaDerived},
    },
    core::algebra::{
        ec::{Curve, Pt2},
        AlgebraicField, HasLookupPoints, Nat, SupportsNatConversions, SupportsU64Conversions,
    },
    mdoc::{
        cbor::{
            mdoc::{FieldLocator, ParsedAttr, ParsedMdoc},
            structure_prover::ConcreteWitness as StructuralWitness,
        },
        proto::{
            hash::constants::{
                K_HASH_INDEX_BITS, K_MAX_SHA_BLOCKS, K_MSO_MAX_BYTES, K_MSO_OFFSET,
                K_MSO_PREIMAGE_LEN, K_TAG32,
            },
            layout,
            mso_attribute::constants::{
                attr_sha_blocks, has_ordered_date_encoding, K_ATTR_INDEX_BITS, K_ATTR_PREIMAGE_LEN,
                K_DATE_SLOT, K_SHA256_BLOCK_SIZE, K_SHA256_PADDING_LEN,
            },
        },
        v2::{
            attribute::{AttributeOp, RequestedAttribute},
            error::MdocProverErrorCode,
            inputs::builder::{AssignmentBuilder, BinaryAssignmentBuilder},
            request::Request,
        },
    },
    runtime::algebra::{
        p256::{P256Element, P256Field},
        q256::Q256Field,
        secp256r1::Secp256r1,
        RuntimeNat,
    },
};

pub(in crate::mdoc::runtime::v2) fn push_witness_hash<N: Nat<4>>(
    request: &Request<'_>,
    parsed: &ParsedMdoc<N>,
) -> Result<Vec<bool>, MdocProverErrorCode> {
    push_witness_hash_impl(request, parsed, None)
}

/// Match the witness to the private width of a validated hash circuit. The
/// ordinary upstream circuit uses the base witness; the structural experiment
/// adds its slot-aware suffix. No other final width is accepted.
pub(in crate::mdoc::runtime::v2) fn push_witness_hash_for_width<N: Nat<4>>(
    request: &Request<'_>,
    parsed: &ParsedMdoc<N>,
    private_bits: usize,
) -> Result<Vec<bool>, MdocProverErrorCode> {
    push_witness_hash_impl(request, parsed, Some(private_bits))
}

fn push_witness_hash_impl<N: Nat<4>>(
    request: &Request<'_>,
    parsed: &ParsedMdoc<N>,
    expected_width: Option<usize>,
) -> Result<Vec<bool>, MdocProverErrorCode> {
    if parsed.cbor_mso.len().saturating_sub(K_MSO_OFFSET) > K_MSO_MAX_BYTES {
        return Err(MdocProverErrorCode::TaggedMsoTooBig);
    }
    let mut builder = BinaryAssignmentBuilder::new();
    // The leading private inputs follow the shared layout table, which the
    // runtime link reads; refuse to produce a witness that drifts from it.
    let at = |position: usize, range: &core::ops::Range<usize>, name: &str| {
        layout::check_at(position, range, name)
            .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)
    };

    // 1. Values shared with the signature circuit, in its order: issuer
    // digest, device x, device y (256 bits each).
    at(
        builder.buffer.len(),
        &layout::hash::ISSUER_DIGEST,
        "issuer digest",
    )?;
    builder.push_nat256(&parsed.issuer_sig_digest);
    at(builder.buffer.len(), &layout::hash::DEVICE_X, "device x")?;
    builder.push_nat256(&parsed.device_pk.0);
    at(builder.buffer.len(), &layout::hash::DEVICE_Y, "device y")?;
    builder.push_nat256(&parsed.device_pk.1);

    // 2. preimage (MSO preimage - bytes as bits) + preimage.len
    let (mso_sha_in, mso_sha_derived) = given_and_derived(&parsed.cbor_mso, K_MAX_SHA_BLOCKS)
        .map_err(|_| MdocProverErrorCode::TaggedMsoTooBig)?;
    let requested = request
        .attributes()
        .first()
        .ok_or(MdocProverErrorCode::InvalidInput)?;
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
    let signed_bytes = &mso_sha_in.padded_preimage;
    let nblocks = mso_sha_in.nblocks;
    let preimage_arr: [u8; K_MSO_PREIMAGE_LEN] = signed_bytes.as_slice().try_into().unwrap();

    at(
        builder.buffer.len(),
        &layout::hash::MSO_PREIMAGE,
        "MSO preimage",
    )?;
    for &b in &preimage_arr {
        builder.push_v8(b);
    }
    at(builder.buffer.len(), &layout::hash::MSO_LEN, "MSO length")?;
    builder.push_bits_len(parsed.cbor_mso.len() as u64, K_HASH_INDEX_BITS);

    // 3. nblocks (bytes as bits)
    at(builder.buffer.len(), &layout::hash::NBLOCKS, "block count")?;
    builder.push_v8(nblocks as u8);
    let end = layout::hash::NBLOCKS.end;
    at(builder.buffer.len(), &(end..end), "end of block count")?;

    // 4. doc_type / valid_from / valid_until / dev_key_info / value_digests offsets
    let preimage_base_offset = K_MSO_OFFSET;
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
    builder.push_bits_len(
        (preimage_base_offset + namespace.key_offset) as u64,
        K_HASH_INDEX_BITS,
    );

    // 5. attribute_witnesses
    push_witness_attrs(
        request.attributes(),
        &attributes,
        &parsed.cbor_mso,
        &mut builder,
    )?;

    // 6. sha_witnesses (MSO preimage hashing)
    builder.push_sha256msg_derived(&mso_sha_derived);

    let Some(private_bits) = expected_width else {
        return Ok(builder.buffer);
    };
    if private_bits == builder.buffer.len() {
        return Ok(builder.buffer);
    }
    if private_bits < builder.buffer.len() {
        return Err(MdocProverErrorCode::WitnessCreationFailure);
    }
    let selected = request
        .attributes()
        .iter()
        .map(|request| {
            if !request.enabled {
                return Ok(None);
            }
            let attr = attributes
                .iter()
                .find(|a| a.name == request.id)
                .ok_or(MdocProverErrorCode::AttributeNotFound)?;
            Ok(Some((
                attr.mso_digest_offset_in_preimage,
                attr.cbor_issuer_signed_item.as_slice(),
            )))
        })
        .collect::<Result<Vec<_>, MdocProverErrorCode>>()?;
    let structure =
        StructuralWitness::derive_slots(&parsed.cbor_mso, namespace.key_offset, &selected)
            .map_err(|_| MdocProverErrorCode::MsoDecodingFailure)?;
    structure.push(|value, bits| builder.push_bits_len(value, bits));
    if builder.buffer.len() != private_bits {
        return Err(MdocProverErrorCode::WitnessCreationFailure);
    }
    Ok(builder.buffer)
}

fn push_witness_attrs(
    req_attrs: &[RequestedAttribute],
    attributes: &[&ParsedAttr],
    signed: &[u8],
    builder: &mut BinaryAssignmentBuilder,
) -> Result<(), MdocProverErrorCode> {
    for (slot, la) in req_attrs.iter().enumerate() {
        let sha_blocks = attr_sha_blocks(slot);
        let padded_len = sha_blocks * K_SHA256_BLOCK_SIZE;
        if !la.enabled {
            push_attribute_witness(
                builder,
                &[0; K_ATTR_PREIMAGE_LEN][..padded_len],
                0,
                0,
                &FieldLocator {
                    slot_position: [0; 4],
                    length: [0; 4],
                    permutation: 0,
                },
                &ShaDerived::from_fn(sha_blocks, || 0),
            );
            continue;
        }
        let pa = attributes
            .iter()
            .find(|attribute| attribute.name == la.id)
            .ok_or(MdocProverErrorCode::AttributeNotFound)?;
        let actual = &pa.cbor_value;
        let operand = &la.cbor_value;
        let relation = match la.op {
            AttributeOp::Eq => actual == operand,
            AttributeOp::Le => actual <= operand,
            AttributeOp::Ge => actual >= operand,
        };
        if !relation
            || (slot == K_DATE_SLOT
                && (actual.len() != operand.len() || !has_ordered_date_encoding(actual)))
        {
            return Err(MdocProverErrorCode::GeneralFailure);
        }
        let item = &pa.cbor_issuer_signed_item;
        if item.len() > padded_len - K_SHA256_PADDING_LEN {
            return Err(MdocProverErrorCode::AttributeTooLong);
        }
        let (attr_sha_in, attr_sha_derived) = given_and_derived(item, sha_blocks)
            .map_err(|_| MdocProverErrorCode::AttributeTooLong)?;
        // The signed MSO holds `bstr(SHA-256(item))` at the digest offset, as
        // the hash circuit checks; an item the issuer did not sign fails here.
        let digest = signed
            .get(K_MSO_OFFSET + pa.mso_digest_offset_in_preimage..)
            .and_then(|tail| {
                tail.strip_prefix(&K_TAG32)
                    .and_then(|digest| digest.get(..32))
            });
        if digest != Some(Sha256::digest(item).as_slice()) {
            return Err(MdocProverErrorCode::GeneralFailure);
        }
        push_attribute_witness(
            builder,
            &attr_sha_in.padded_preimage,
            item.len(),
            K_MSO_OFFSET + pa.mso_digest_offset_in_preimage,
            &pa.field_locator,
            &attr_sha_derived,
        );
    }
    Ok(())
}

fn push_attribute_witness(
    builder: &mut BinaryAssignmentBuilder,
    preimage: &[u8],
    preimage_len: usize,
    digest_offset: usize,
    locator: &FieldLocator,
    sha_derived: &ShaDerived<u32>,
) {
    for &byte in preimage {
        builder.push_v8(byte);
    }
    builder.push_bits_len(preimage_len as u64, K_ATTR_INDEX_BITS);
    builder.push_bits_len(digest_offset as u64, K_HASH_INDEX_BITS);
    for &position in &locator.slot_position {
        builder.push_bits_len(position as u64, K_ATTR_INDEX_BITS);
    }
    for &length in &locator.length {
        builder.push_bits_len(length as u64, K_ATTR_INDEX_BITS);
    }
    for i in 0..4 {
        builder.push_bits_len(((locator.permutation >> (2 * i)) & 3) as u64, 2);
    }
    builder.push_sha256msg_derived(sha_derived);
}

pub(in crate::mdoc::runtime::v2) fn push_witness_sig(
    runtime_field: &P256Field,
    q256: &Q256Field,
    secp256r1: &Secp256r1<P256Field>,
    request: &Request<'_>,
    parsed: &ParsedMdoc<RuntimeNat<4>>,
) -> Result<Vec<P256Element>, MdocProverErrorCode> {
    // A signature without a witness (an exceptional point of the affine
    // layout) is a witness failure; one the circuit would reject is the
    // circuit's own `GeneralFailure`, found here before any randomness.
    let witness = |pk: &(P256Element, P256Element),
                   e: &RuntimeNat<4>,
                   r: &RuntimeNat<4>,
                   s: &RuntimeNat<4>| {
        let (given, derived) = try_witness(secp256r1, pk, e, r, s, runtime_field, q256)
            .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;
        if signature_accepted(runtime_field, secp256r1, &given, &derived, r) {
            Ok((given, derived))
        } else {
            Err(MdocProverErrorCode::GeneralFailure)
        }
    };
    let (issuer_sig_given, issuer_sig_derived) = witness(
        request.issuer_pk(),
        &parsed.issuer_sig_digest,
        &parsed.issuer_sig_r,
        &parsed.issuer_sig_s,
    )?;
    let (device_sig_given, device_sig_derived) = witness(
        &(
            runtime_field.reduce_nat(&parsed.device_pk.0),
            runtime_field.reduce_nat(&parsed.device_pk.1),
        ),
        &parsed.device_sig_digest,
        &parsed.device_sig_r,
        &parsed.device_sig_s,
    )?;

    for index in 0..1usize << layout::sig::ERS_BITS {
        let expected = runtime_field.subf(
            &runtime_field.u64_to_element(layout::sig::ERS_SCALE.unsigned_abs() * index as u64),
            &runtime_field.u64_to_element(layout::sig::ERS_OFFSET.unsigned_abs()),
        );
        if runtime_field.lookup_point(layout::sig::ERS_TABLE_SIZE, index) != expected {
            return Err(MdocProverErrorCode::WitnessCreationFailure);
        }
    }
    let mut builder = AssignmentBuilder::new(runtime_field);

    // The leading private inputs are the shared values of the layout table,
    // which the runtime link reads; refuse to drift from it.
    let at = |position: usize, range: &core::ops::Range<usize>| {
        layout::check_at(position, range, "signature input")
            .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)
    };

    // 1. issuer_sig_digest
    at(builder.buffer.len(), &layout::sig::ISSUER_DIGEST)?;
    builder.push_nat_256_bits(&parsed.issuer_sig_digest);

    // 2. device_pk
    at(builder.buffer.len(), &layout::sig::DEVICE_X)?;
    builder.push_nat_256_bits(&parsed.device_pk.0);
    at(builder.buffer.len(), &layout::sig::DEVICE_Y)?;
    builder.push_nat_256_bits(&parsed.device_pk.1);
    at(
        builder.buffer.len(),
        &(layout::SHARED_BITS..layout::SHARED_BITS),
    )?;

    // 3. issuer_sig_given
    builder.push_ecdsa_signature(
        &issuer_sig_given,
        &layout::sig::ISSUER_R,
        &layout::sig::ISSUER_ERS,
    )?;

    // 4. device_sig_given
    builder.push_ecdsa_signature(
        &device_sig_given,
        &layout::sig::DEVICE_R,
        &layout::sig::DEVICE_ERS,
    )?;

    // 5. issuer_sig_derived
    builder.push_ecdsa_derived(&issuer_sig_derived);

    // 6. device_sig_derived
    builder.push_ecdsa_derived(&device_sig_derived);

    Ok(builder.buffer)
}

/// Whether the signature circuit accepts this honestly encoded signature
/// witness: the key and `R = (r, y)` lie on the curve, `r < n`, and the final
/// accumulated point `e G + r PK - s R` is the point at infinity. That point is
/// zero exactly when `R` is the recovered point `(e/s) G + (r/s) PK`. The
/// circuit's other assertions hold by construction of the witness or were
/// checked by [`try_witness`] (the nonzero inverses).
fn signature_accepted(
    f: &P256Field,
    curve: &Secp256r1<P256Field>,
    given: &Given<P256Element>,
    derived: &Derived<P256Element>,
    r: &RuntimeNat<4>,
) -> bool {
    let on_curve = |(x, y): &Pt2<P256Field>| {
        f.mulf(y, y) == f.addf(&f.mulf(&f.addf(&f.mulf(x, x), curve.a()), x), curve.b())
    };
    let (ax, _, az) = &derived.slicing.round[0];
    on_curve(&given.pkxy)
        && on_curve(&given.rxy)
        && *r < curve.order()
        && f.is_zero(ax)
        && f.is_zero(az)
}
