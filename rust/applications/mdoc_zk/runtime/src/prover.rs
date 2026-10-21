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

use mdoc_zk_circuits::cbor::mdoc::{parse_mdoc, MdocParseError, ParsedMdoc};
use runtime_algebra::{
    gf2_128::Gf2_128Field, lch14_reed_solomon::Lch14InterpolatorFactory, p256::P256Field,
    reed_solomon::FftInterpolatorFactory, secp256r1::Secp256r1, SupportsFFT,
};
use runtime_random::{RandomEngine, Transcript};
use runtime_zk::ZkProver;

use crate::{
    attribute::{AttributeOp, RequestedAttribute},
    MdocProverErrorCode, ZkSpecStruct,
};

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
) -> Result<Vec<u8>, MdocProverErrorCode> {
    let mut rng = runtime_random::SecureRandomEngine::new();
    run_mdoc_prover_inner(
        zk_spec,
        circuits_compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        &mut rng,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover_ext(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
) -> Result<(Vec<u8>, Vec<RequestedAttribute>), MdocProverErrorCode> {
    let mut rng = runtime_random::SecureRandomEngine::new();
    run_mdoc_prover_inner_ext(
        zk_spec,
        circuits_compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        &mut rng,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover_inner<RNG: RandomEngine>(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    rng: &mut RNG,
) -> Result<Vec<u8>, MdocProverErrorCode> {
    run_mdoc_prover_inner_ext(
        zk_spec,
        circuits_compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        rng,
    )
    .map(|(proof, _)| proof)
}

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover_inner_ext<RNG: RandomEngine>(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    rng: &mut RNG,
) -> Result<(Vec<u8>, Vec<RequestedAttribute>), MdocProverErrorCode> {
    let version = zk_spec.version;
    let (config_hash, config_sig) = crate::ligero_configs(zk_spec);
    if !crate::is_supported_version(version) {
        return Err(MdocProverErrorCode::InvalidZkSpecVersion);
    }
    if !crate::utils::is_iso_datetime_utc(now.as_bytes())
        || doc_type.is_empty()
        || doc_type.len() > 32
    {
        return Err(MdocProverErrorCode::InvalidInput);
    }
    if !crate::same_namespace(attrs) || attrs.iter().any(|a| a.namespace_id.is_empty()) {
        return Err(MdocProverErrorCode::NamespacesMissing);
    }
    let num_attr_sha_blocks = if version >= 8 {
        mdoc_zk_proto::mso_attribute::constants::attr_sha_blocks_for_circuit(
            zk_spec.num_attributes,
            zk_spec.pnym,
        )
    } else {
        mdoc_zk_proto::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS
    };
    let max_attr_len =
        mdoc_zk_proto::mso_attribute::constants::max_attr_cbor_len(num_attr_sha_blocks);
    let max_pnym_attr_len = mdoc_zk_proto::mso_attribute::constants::max_attr_cbor_len(
        mdoc_zk_proto::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS,
    );
    if version < 8 {
        if zk_spec.pnym {
            return Err(MdocProverErrorCode::InvalidZkSpecVersion);
        }
        if attrs.len() != zk_spec.num_attributes || zk_spec.num_attributes == 0 {
            return Err(MdocProverErrorCode::InvalidRequest);
        }
        for a in attrs {
            if a.op == AttributeOp::Pnym || !a.context.is_empty() || a.id.is_empty() {
                return Err(MdocProverErrorCode::InvalidRequest);
            }
            if a.op != AttributeOp::Eq {
                return Err(MdocProverErrorCode::UnsupportedComparison);
            }
            if !crate::attr_encoding_fits(
                &a.id,
                &a.cbor_value,
                mdoc_zk_proto::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS,
            ) {
                return Err(MdocProverErrorCode::AttributeTooLong);
            }
        }
    } else {
        let num_pnym = attrs.iter().filter(|a| a.op == AttributeOp::Pnym).count();
        let num_reg = attrs.len() - num_pnym;
        if zk_spec.pnym {
            let valid_reg = match zk_spec.num_attributes {
                1 => num_reg == 1,
                4 => (2..=4).contains(&num_reg),
                _ => return Err(MdocProverErrorCode::InvalidZkSpecVersion),
            };
            if num_pnym != 1 || !valid_reg {
                return Err(MdocProverErrorCode::InvalidRequest);
            }
        } else {
            if num_pnym > 0 {
                return Err(MdocProverErrorCode::InvalidRequest);
            }
            let valid_count = match zk_spec.num_attributes {
                1 => num_reg == 1,
                2 => (1..=2).contains(&num_reg),
                4 => (2..=4).contains(&num_reg),
                n => num_reg == n && num_reg > 0,
            };
            if !valid_count {
                return Err(MdocProverErrorCode::InvalidRequest);
            }
        }
        for a in attrs {
            if a.op == AttributeOp::Pnym {
                if a.id != b"pnym_seed" {
                    return Err(MdocProverErrorCode::InvalidRequest);
                }
                if a.context.is_empty()
                    || a.context.len()
                        > mdoc_zk_proto::mso_attribute::constants::K_PNYM_CONTEXT_MAX
                {
                    return Err(MdocProverErrorCode::PnymContextMissing);
                }
            } else {
                if !a.context.is_empty() || a.id.is_empty() {
                    return Err(MdocProverErrorCode::InvalidRequest);
                }
                if !crate::circuit_supports(&a.cbor_value) {
                    return Err(MdocProverErrorCode::UnsupportedAttribute);
                }
                if matches!(a.op, AttributeOp::Le | AttributeOp::Ge)
                    && !crate::circuit_supports_comparison(&a.cbor_value)
                {
                    return Err(MdocProverErrorCode::UnsupportedComparison);
                }
                if !crate::attr_encoding_fits(&a.id, &a.cbor_value, num_attr_sha_blocks) {
                    return Err(MdocProverErrorCode::AttributeTooLong);
                }
            }
        }
    }

    let p256 = P256Field::new();
    let issuer_pk = (
        crate::parse_pk_coordinate(pkx, &p256).map_err(|_| MdocProverErrorCode::InvalidInput)?,
        crate::parse_pk_coordinate(pky, &p256).map_err(|_| MdocProverErrorCode::InvalidInput)?,
    );

    let mac_ap = crate::generate_mac_ap(rng);

    let mut tp = Transcript::new(transcript);
    let p256_2 = runtime_algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig = FftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let q256 = runtime_algebra::Q256Field::new();
    let secp256r1 = Secp256r1::new(&p256);

    let gf2 = Gf2_128Field::new();
    let sf_hash =
        runtime_algebra::subfield::BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
    let make_interpolator_hash = Lch14InterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = crate::proto::decompress_circuits(circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;

    let parsed: ParsedMdoc<runtime_algebra::RuntimeNat<4>> =
        parse_mdoc(mdoc_bytes, transcript, doc_type).map_err(|err| match err {
            MdocParseError::TooBig => MdocProverErrorCode::TaggedMsoTooBig,
            _ => MdocProverErrorCode::MsoDecodingFailure,
        })?;

    let mut resolved_attrs = attrs.to_vec();
    for ra in &mut resolved_attrs {
        // Evaluate every requested predicate on the host before doing any proving work: an
        // unsatisfiable request is a caller error (`PredicateNotSatisfied`), not a proof
        // failure. The circuit enforces the same relation on the issuer-signed bytes.
        match ra.op {
            AttributeOp::Pnym => {
                let pa = parsed
                    .get_attribute(b"pnym_seed")
                    .ok_or(MdocProverErrorCode::PnymSeedMissing)?;
                if pa.cbor_issuer_signed_item.len() > max_pnym_attr_len {
                    return Err(MdocProverErrorCode::AttributeTooLong);
                }
                let seed = mdoc_zk_circuits::cbor::pnym_seed_of(pa)
                    .map_err(|_| MdocProverErrorCode::PnymSeedMalformed)?;
                let digest = mdoc_zk_circuits::cbor::compute_pseudonym(&seed, &ra.context);
                let pnym_cbor = mdoc_zk_circuits::cbor::encode_pnym_cbor_value(&digest);
                // A verifier may pre-fill the expected pseudonym ("prove you are X").
                if !ra.cbor_value.is_empty() && ra.cbor_value != pnym_cbor {
                    return Err(MdocProverErrorCode::PredicateNotSatisfied);
                }
                ra.cbor_value = pnym_cbor;
            }
            AttributeOp::Eq => {
                let pa = parsed
                    .get_attribute(&ra.id)
                    .ok_or(MdocProverErrorCode::AttributeNotFound)?;
                if pa.cbor_issuer_signed_item.len() > max_attr_len {
                    return Err(MdocProverErrorCode::AttributeTooLong);
                }
                if pa.cbor_value != ra.cbor_value {
                    return Err(MdocProverErrorCode::PredicateNotSatisfied);
                }
            }
            AttributeOp::Le | AttributeOp::Ge => {
                // Only reachable for version >= 8; request validation above rejects these
                // operators for earlier versions.
                let pa = parsed
                    .get_attribute(&ra.id)
                    .ok_or(MdocProverErrorCode::AttributeNotFound)?;
                if pa.cbor_issuer_signed_item.len() > max_attr_len {
                    return Err(MdocProverErrorCode::AttributeTooLong);
                }
                if !crate::circuit_supports_comparison(&pa.cbor_value)
                    || pa.cbor_value.len() != ra.cbor_value.len()
                {
                    return Err(MdocProverErrorCode::UnsupportedComparison);
                }
                let satisfied = if ra.op == AttributeOp::Le {
                    pa.cbor_value <= ra.cbor_value
                } else {
                    pa.cbor_value >= ra.cbor_value
                };
                if !satisfied {
                    return Err(MdocProverErrorCode::PredicateNotSatisfied);
                }
            }
        }
    }

    let circuit_attrs = if version >= 8 {
        crate::utils::pad_request_attrs(&resolved_attrs, zk_spec.num_attributes)
    } else {
        resolved_attrs.clone()
    };

    let witness_hash = crate::push_witness_hash(version, &gf2, &circuit_attrs, &parsed, &mac_ap)?;
    let witness_sig = crate::push_witness_sig(
        version, &p256, &q256, &secp256r1, &issuer_pk, &parsed, &mac_ap,
    )?;

    let sf_sig = runtime_algebra::p256::P256Subfield::new(&p256);

    let prover_hash = ZkProver::<2, _>::new(c_hash, config_hash);
    let (commit_hash, geom_hash) = prover_hash.commit(
        &witness_hash,
        &runtime_zk::common::ZkContext {
            f: &gf2,
            make_interpolator: &make_interpolator_hash,
        },
        &mut tp,
        rng,
        &sf_hash,
    );

    let prover_sig = ZkProver::<4, _>::new(c_sig, config_sig);
    let (commit_sig, geom_sig) = prover_sig.commit(
        &witness_sig,
        &runtime_zk::common::ZkContext {
            f: &p256,
            make_interpolator: &make_interpolator_sig,
        },
        &mut tp,
        rng,
        &sf_sig,
    );

    let av_val = tp.u128();

    let macs = crate::push_macs(
        &gf2,
        version,
        &parsed.issuer_sig_digest,
        &parsed.device_pk,
        av_val,
        &mac_ap,
    );
    let hash_pub_inputs = crate::push_input_hash(
        version,
        &gf2,
        &circuit_attrs,
        now.as_bytes(),
        &macs,
        av_val,
        false,
        doc_type.as_bytes(),
    );
    let sig_pub_inputs = crate::push_input_sig(
        version,
        &p256,
        &issuer_pk,
        &parsed.device_sig_digest,
        &macs,
        av_val,
    );

    let proof_hash = prover_hash
        .prove(
            hash_pub_inputs,
            witness_hash,
            &commit_hash,
            &mut tp,
            &runtime_zk::common::ZkContext {
                f: &gf2,
                make_interpolator: &make_interpolator_hash,
            },
        )
        .map_err(|e| {
            eprintln!("prover_hash.prove failed: {e}");
            MdocProverErrorCode::GeneralFailure
        })?;

    let proof_sig = prover_sig
        .prove(
            sig_pub_inputs,
            witness_sig,
            &commit_sig,
            &mut tp,
            &runtime_zk::common::ZkContext {
                f: &p256,
                make_interpolator: &make_interpolator_sig,
            },
        )
        .map_err(|e| {
            eprintln!("prover_sig.prove failed: {e}");
            MdocProverErrorCode::GeneralFailure
        })?;

    let geom = crate::proto::MdocProofGeometry {
        geom_hash,
        geom_sig,
    };
    let proof = crate::proto::MdocProof {
        macs,
        proof_hash,
        proof_sig,
    };
    let out = proof
        .write(&geom, &gf2, &sf_hash, &p256, &sf_sig)
        .map_err(|e| {
            eprintln!("proof.write failed: {e}");
            MdocProverErrorCode::GeneralFailure
        })?;
    Ok((out, resolved_attrs))
}
