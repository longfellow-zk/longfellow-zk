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

//! Longfellow v1 application prover.

use super::ZkSpecStruct;
use crate::{
    mdoc::{
        circuits::cbor::mdoc::{parse_mdoc, MdocParseError, ParsedMdoc},
        runtime::v1::{MdocProverErrorCode, RequestedAttribute},
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
        zk_v1::ZkProver,
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
    let version = zk_spec.version;
    if !zk_spec.is_valid() {
        return Err(MdocProverErrorCode::InvalidZkSpecVersion);
    }
    let (config_hash, config_sig) = super::ligero_configs(zk_spec);
    if !super::attribute::same_namespace(attrs) {
        return Err(MdocProverErrorCode::NamespacesMissing);
    }
    let p256 = P256Field::new();
    let issuer_pk = (
        super::key::parse_pk_coordinate(pkx, &p256)
            .map_err(|_| MdocProverErrorCode::InvalidInput)?,
        super::key::parse_pk_coordinate(pky, &p256)
            .map_err(|_| MdocProverErrorCode::InvalidInput)?,
    );

    let mac_ap = super::mac::generate_mac_ap(rng);

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

    let (c_sig, c_hash) = super::circuits::decompress_circuits(circuits_compressed, &p256, &gf2)
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

    let witness_hash = super::inputs::push_witness_hash(&gf2, version, attrs, &parsed, &mac_ap)?;
    let witness_sig =
        super::inputs::push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed, &mac_ap);

    let sf_sig = crate::runtime::algebra::p256::P256Subfield::new(&p256);

    let prover_hash = ZkProver::<2, _>::new(c_hash, config_hash);
    let (commit_hash, geom_hash) = prover_hash.commit(
        &witness_hash,
        &crate::runtime::zk_v1::common::ZkContext {
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
        &crate::runtime::zk_v1::common::ZkContext {
            f: &p256,
            make_interpolator: &make_interpolator_sig,
        },
        &mut tp,
        rng,
        &sf_sig,
    );

    let av_val = tp.u128();

    let macs = super::mac::push_macs(
        &gf2,
        &parsed.issuer_sig_digest,
        &parsed.device_pk,
        av_val,
        &mac_ap,
    );
    let hash_pub_inputs =
        super::inputs::push_input_hash(version, &gf2, attrs, now.as_bytes(), &macs, av_val);
    let sig_pub_inputs =
        super::inputs::push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest, &macs, av_val);

    let proof_hash = prover_hash
        .prove(
            hash_pub_inputs,
            witness_hash,
            &commit_hash,
            &mut tp,
            &crate::runtime::zk_v1::common::ZkContext {
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
            &crate::runtime::zk_v1::common::ZkContext {
                f: &p256,
                make_interpolator: &make_interpolator_sig,
            },
        )
        .map_err(|e| {
            eprintln!("prover_sig.prove failed: {e}");
            MdocProverErrorCode::GeneralFailure
        })?;

    let geom = super::proto::MdocProofGeometry {
        geom_hash,
        geom_sig,
    };
    let proof = super::proto::MdocProof {
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
    Ok(out)
}
