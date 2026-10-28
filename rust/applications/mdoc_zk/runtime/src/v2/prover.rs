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

//! Longfellow v2 application prover.

use super::{
    inputs::{
        public_inputs_fit, push_input_hash, push_input_sig, push_witness_hash, push_witness_sig,
    },
    proto::{MdocProof, MdocProofGeometry},
    ZkSpecStruct,
};
use crate::{
    mdoc::{
        circuits::cbor::mdoc::{parse_mdoc, MdocParseError, ParsedMdoc},
        runtime::v2::{
            attribute::{circuit_supports, same_namespace},
            circuits::for_spec,
            key::parse_pk_coordinate,
            mac::{generate_mac_ap, push_macs},
            MdocProverErrorCode, RequestedAttribute,
        },
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            secp256r1::Secp256r1,
            SupportsFFT,
        },
        random::{RandomEngine, Transcript},
        zk_v2::{ZkContext, ZkProver},
    },
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
    let mut rng = crate::runtime::random::SecureRandomEngine::new();
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
    if !zk_spec.supports_version() {
        return Err(MdocProverErrorCode::InvalidZkSpecVersion);
    }
    if attrs.len() != zk_spec.num_attributes {
        return Err(MdocProverErrorCode::InvalidInput);
    }
    let (config_hash, config_sig) = zk_spec.configs();
    if !same_namespace(attrs) {
        return Err(MdocProverErrorCode::NamespacesMissing);
    }
    if !public_inputs_fit(attrs, now.as_bytes(), doc_type.as_bytes()) {
        return Err(MdocProverErrorCode::InvalidInput);
    }
    for a in attrs {
        if !circuit_supports(&a.cbor_value) {
            return Err(MdocProverErrorCode::UnsupportedAttribute);
        }
    }

    let p256 = P256Field::new();
    let issuer_pk = (
        parse_pk_coordinate(pkx, &p256).map_err(|_| MdocProverErrorCode::InvalidInput)?,
        parse_pk_coordinate(pky, &p256).map_err(|_| MdocProverErrorCode::InvalidInput)?,
    );

    let mac_ap = generate_mac_ap(rng);

    let mut tp = Transcript::new(transcript);
    let p256_2 = crate::runtime::algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let q256 = crate::runtime::algebra::Q256Field::new();
    let secp256r1 = Secp256r1::new(&p256);

    let gf2 = Gf2_128Field::new();
    let sf_hash = crate::runtime::algebra::subfield_v1::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator_hash = BinaryInterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = for_spec(zk_spec, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;

    let parsed: ParsedMdoc<crate::runtime::algebra::RuntimeNat<4>> =
        parse_mdoc(mdoc_bytes, transcript, doc_type).map_err(|err| match err {
            MdocParseError::TooBig => MdocProverErrorCode::TaggedMsoTooBig,
            _ => MdocProverErrorCode::MsoDecodingFailure,
        })?;

    for req_attr in attrs {
        if parsed.get_attribute(&req_attr.id).is_none() {
            return Err(MdocProverErrorCode::AttributeNotFound);
        }
    }

    let witness_hash = push_witness_hash(&gf2, attrs, &parsed, &mac_ap)?;
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed, &mac_ap)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;


    let context_hash = ZkContext {
        f: &gf2,
        domain: &make_interpolator_hash,
    };
    let context_sig = ZkContext {
        f: &p256,
        domain: &make_interpolator_sig,
    };

    let prover_hash = ZkProver::<2, _>::new_full_field(c_hash, config_hash);
    let (commit_hash, geom_hash) = prover_hash
        .commit(witness_hash, &context_hash, &mut tp, rng)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    let prover_sig = ZkProver::<4, _>::new(c_sig, config_sig);
    let (commit_sig, geom_sig) = prover_sig
        .commit(witness_sig, &context_sig, &mut tp, rng)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    let av_val = tp.u128();

    let macs = push_macs(
        &parsed.issuer_sig_digest,
        &parsed.device_pk,
        av_val,
        &mac_ap,
    );
    let hash_pub_inputs = push_input_hash(
        &gf2,
        attrs,
        now.as_bytes(),
        &macs,
        av_val,
        false,
        doc_type.as_bytes(),
    );
    let sig_pub_inputs =
        push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest, &macs, av_val);

    let proof_hash = prover_hash
        .prove(&hash_pub_inputs, commit_hash, &mut tp, &context_hash)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    let proof_sig = prover_sig
        .prove(&sig_pub_inputs, commit_sig, &mut tp, &context_sig)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    let geom = MdocProofGeometry {
        geom_hash,
        geom_sig,
    };
    let proof = MdocProof {
        macs,
        proof_hash,
        proof_sig,
    };
    proof
        .write(&geom, &gf2, &p256)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)
}
