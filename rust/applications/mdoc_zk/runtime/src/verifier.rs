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

use core_algebra::Nat;
use runtime_algebra::{
    gf2_128::Gf2_128Field, lch14_reed_solomon::Lch14InterpolatorFactory, p256::P256Field,
    reed_solomon::FftInterpolatorFactory, SupportsFFT,
};
use runtime_random::{transcript::Transcript, RandomEngine};
use runtime_zk::ZkVerifier;

use crate::{
    attribute::AttributeOp,
    push_input_hash, push_input_sig,
    utils::{
        attr_encoding_fits, circuit_supports, circuit_supports_comparison, is_iso_datetime_utc,
        pad_request_attrs, parse_pk_coordinate, same_namespace,
    },
    MdocProof, MdocProofGeometry, MdocVerifierErrorCode, RequestedAttribute, ZkSpecStruct,
};

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_verifier(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    proof_bytes: &[u8],
) -> Result<(), MdocVerifierErrorCode> {
    run_mdoc_verifier_inner(
        zk_spec,
        circuits_compressed,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        proof_bytes,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_verifier_inner(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    proof_bytes: &[u8],
) -> Result<(), MdocVerifierErrorCode> {
    let version = zk_spec.version;
    let (config_hash, config_sig) = crate::ligero_configs(zk_spec);
    if !crate::is_supported_version(version) {
        return Err(MdocVerifierErrorCode::InvalidZkSpecVersion);
    }
    if !is_iso_datetime_utc(now.as_bytes()) || doc_type.len() > 32 {
        return Err(MdocVerifierErrorCode::InvalidInput);
    }
    if !same_namespace(attrs) {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }
    if attrs.iter().any(|a| a.namespace_id.is_empty()) {
        return Err(MdocVerifierErrorCode::InvalidRequest);
    }
    if version >= 8 {
        let num_attr_sha_blocks =
            mdoc_zk_proto::mso_attribute::constants::attr_sha_blocks_for_circuit(
                zk_spec.num_attributes,
                zk_spec.pnym,
            );
        let num_pnym = attrs.iter().filter(|a| a.op == AttributeOp::Pnym).count();
        let num_reg = attrs.len() - num_pnym;
        if zk_spec.pnym {
            if !matches!(zk_spec.num_attributes, 1 | 4) {
                return Err(MdocVerifierErrorCode::InvalidZkSpecVersion);
            }
            if attrs.is_empty() {
                return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
            }
            let valid_reg = match zk_spec.num_attributes {
                1 => num_reg == 1,
                4 => (2..=4).contains(&num_reg),
                _ => false,
            };
            if num_pnym != 1 || !valid_reg {
                return Err(MdocVerifierErrorCode::InvalidRequest);
            }
        } else {
            if num_pnym > 0 {
                return Err(MdocVerifierErrorCode::InvalidRequest);
            }
            let valid_count = match zk_spec.num_attributes {
                1 => num_reg == 1,
                2 => (1..=2).contains(&num_reg),
                4 => (2..=4).contains(&num_reg),
                n => num_reg == n && num_reg > 0,
            };
            if !valid_count {
                return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
            }
        }
        for a in attrs {
            if a.op == AttributeOp::Pnym {
                if a.id != b"pnym_seed"
                    || a.context.is_empty()
                    || a.context.len()
                        > mdoc_zk_proto::mso_attribute::constants::K_PNYM_CONTEXT_MAX
                    || a.cbor_value.len()
                        != mdoc_zk_proto::mso_attribute::constants::K_PNYM_VALUE_LEN
                    || a.cbor_value.get(..2) != Some(&[0x58, 0x20])
                {
                    return Err(MdocVerifierErrorCode::InvalidRequest);
                }
                if !attr_encoding_fits(
                    &a.id,
                    &a.cbor_value,
                    mdoc_zk_proto::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS,
                ) {
                    return Err(MdocVerifierErrorCode::UnsupportedAttribute);
                }
            } else {
                if !a.context.is_empty() || a.id.is_empty() {
                    return Err(MdocVerifierErrorCode::InvalidRequest);
                }
                if !circuit_supports(&a.cbor_value) {
                    return Err(MdocVerifierErrorCode::UnsupportedAttribute);
                }
                if matches!(a.op, AttributeOp::Le | AttributeOp::Ge)
                    && !circuit_supports_comparison(&a.cbor_value)
                {
                    return Err(MdocVerifierErrorCode::UnsupportedComparison);
                }
                if !attr_encoding_fits(&a.id, &a.cbor_value, num_attr_sha_blocks) {
                    return Err(MdocVerifierErrorCode::UnsupportedAttribute);
                }
            }
        }
    } else {
        // For prior versions (version < 8), doc_type and namespace checks are not supported by the
        // circuit to save constraints. Instead, the external verifier computes the ISO
        // 18013-5 standard DeviceAuthentication / COSE_Sign1 transcript hash (which
        // incorporates `doc_type` and the session transcript) and feeds the resulting
        // digest (`e2_val`) as a public input into the signature verification circuit. In
        // current circuits (version >= 8), doc_type and namespaces are supported by the
        // circuit directly as public inputs: in addition to checking the transcript
        // hash, the circuit asserts that the doc_type is the one stored in the document.
        if zk_spec.pnym {
            return Err(MdocVerifierErrorCode::InvalidZkSpecVersion);
        }
        if attrs.len() != zk_spec.num_attributes || zk_spec.num_attributes == 0 {
            return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
        }
        for a in attrs {
            if a.op == AttributeOp::Pnym || !a.context.is_empty() || a.id.is_empty() {
                return Err(MdocVerifierErrorCode::InvalidRequest);
            }
            if a.op != AttributeOp::Eq {
                return Err(MdocVerifierErrorCode::UnsupportedComparison);
            }
            if !attr_encoding_fits(
                &a.id,
                &a.cbor_value,
                mdoc_zk_proto::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS,
            ) {
                return Err(MdocVerifierErrorCode::UnsupportedAttribute);
            }
        }
    }

    let p256 = P256Field::new();
    let pk_x_elt =
        parse_pk_coordinate(pkx, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?;
    let pk_y_elt =
        parse_pk_coordinate(pky, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?;

    let p256_2 = runtime_algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig = FftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let gf2 = Gf2_128Field::new();
    let sf_hash =
        runtime_algebra::subfield::BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
    let make_interpolator_hash = Lch14InterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = crate::proto::decompress_circuits(circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;

    let verifier_hash = ZkVerifier::<2, _>::new(c_hash, config_hash);
    let geom_hash = verifier_hash.geometry(&runtime_zk::common::ZkContext {
        f: &gf2,
        make_interpolator: &make_interpolator_hash,
    });

    let verifier_sig = ZkVerifier::<4, _>::new(c_sig, config_sig);
    let geom_sig = verifier_sig.geometry(&runtime_zk::common::ZkContext {
        f: &p256,
        make_interpolator: &make_interpolator_sig,
    });

    let geom = MdocProofGeometry {
        geom_hash,
        geom_sig,
    };

    let sf_sig = runtime_algebra::p256::P256Subfield::new(&p256);
    let (remaining, proof) = MdocProof::read(proof_bytes, &geom, &gf2, &sf_hash, &p256, &sf_sig)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;

    if !remaining.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }

    let mut tp = Transcript::new(transcript);

    verifier_hash.recv_commitment(
        &proof.proof_hash,
        &mut tp,
        &runtime_zk::common::ZkContext {
            f: &gf2,
            make_interpolator: &make_interpolator_hash,
        },
    );
    verifier_sig.recv_commitment(
        &proof.proof_sig,
        &mut tp,
        &runtime_zk::common::ZkContext {
            f: &p256,
            make_interpolator: &make_interpolator_sig,
        },
    );

    let av_buf = tp.bytes(16);
    let av_val = u128::from_le_bytes(av_buf.try_into().unwrap());

    let circuit_attrs = if version >= 8 {
        pad_request_attrs(attrs, zk_spec.num_attributes)
    } else {
        attrs.to_vec()
    };

    let pub_inputs_hash = push_input_hash(
        version,
        &gf2,
        &circuit_attrs,
        now.as_bytes(),
        &proof.macs,
        av_val,
        false,
        doc_type.as_bytes(),
    );

    if pub_inputs_hash.len() != verifier_hash.circuit.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    verifier_hash
        .verify(
            pub_inputs_hash,
            &proof.proof_hash,
            &mut tp,
            &runtime_zk::common::ZkContext {
                f: &gf2,
                make_interpolator: &make_interpolator_hash,
            },
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    let digest = mdoc_zk_circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = runtime_algebra::RuntimeNat::<4>::from_bytes_be(&digest);

    let pub_inputs_sig = push_input_sig(
        version,
        &p256,
        &(pk_x_elt, pk_y_elt),
        &e2_val,
        &proof.macs,
        av_val,
    );

    if pub_inputs_sig.len() != verifier_sig.circuit.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    verifier_sig
        .verify(
            pub_inputs_sig,
            &proof.proof_sig,
            &mut tp,
            &runtime_zk::common::ZkContext {
                f: &p256,
                make_interpolator: &make_interpolator_sig,
            },
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    Ok(())
}
