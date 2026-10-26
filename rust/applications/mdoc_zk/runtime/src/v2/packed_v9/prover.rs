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

//! Experimental packed-v9 application prover with a direct-field signature proof.

use super::{
    super::inputs::{
        public_inputs_fit, push_input_hash_packed, push_input_sig, push_witness_hash_packed,
        push_witness_sig,
    },
    proto::{MdocProof, MdocProofGeometry},
    PackedV9Spec,
};
use crate::{
    mdoc::{
        circuits::cbor::mdoc::{parse_mdoc, MdocParseError, ParsedMdoc},
        runtime::v2::{
            attribute::{circuit_supports, same_namespace},
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
    zk_spec: &PackedV9Spec,
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
    zk_spec: &PackedV9Spec,
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
    run_mdoc_prover_inner_with_window(
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
        None,
    )
}
#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover_inner_with_window<RNG: RandomEngine>(
    zk_spec: &PackedV9Spec,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    rng: &mut RNG,
    boolean_window: Option<usize>,
) -> Result<Vec<u8>, MdocProverErrorCode> {
    #[cfg(feature = "bench-profile")]
    let mut profile = crate::util::profile::Timer::new("app.prover.setup_and_witness");
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
    let sf_hash = crate::runtime::algebra::subfield::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator_hash = BinaryInterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = super::provider::load_trusted(zk_spec, circuits_compressed, &p256, &gf2)
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

    let mut witness_hash = push_witness_hash_packed(&gf2, attrs, &parsed, &mac_ap)?;
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed, &mac_ap)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    let hash_public_bits = push_input_hash_packed(
        &gf2,
        attrs,
        now.as_bytes(),
        false,
        doc_type.as_bytes(),
    );
    zk_spec
        .manifest
        .extend_witness(&hash_public_bits, &mut witness_hash)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let sf_sig = crate::runtime::algebra::p256::P256Subfield::new(&p256);

    let context_hash = ZkContext {
        f: &gf2,
        domain: &make_interpolator_hash,
    };
    let context_sig = ZkContext {
        f: &p256,
        domain: &make_interpolator_sig,
    };

    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.hash_commit");
    let mut prover_hash = crate::runtime::zk_v2::packed::PackedCircuit::new(
        c_hash,
        config_hash,
        6,
        zk_spec.manifest.digest(),
    )
    .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;
    if let Some(window) = boolean_window {
        prover_hash = prover_hash
            .with_boolean_window(window)
            .map_err(|_| MdocProverErrorCode::InvalidInput)?;
    }
    let (commit_hash, geom_hash) = prover_hash
        .commit(
            witness_hash,
            mac_ap
                .iter()
                .flatten()
                .copied()
                .map(crate::runtime::algebra::gf2_128::Gf2_128::from)
                .collect(),
            &context_hash,
            &mut tp,
            rng,
            &sf_hash,
        )
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.signature_commit");
    let prover_sig = ZkProver::<4, _>::new(c_sig, config_sig);
    let (commit_sig, geom_sig) = prover_sig
        .commit(&witness_sig, &context_sig, &mut tp, rng, &sf_sig)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.public_statement");
    let av_val = tp.u128();

    let macs = push_macs(
        &parsed.issuer_sig_digest,
        &parsed.device_pk,
        av_val,
        &mac_ap,
    );
    let sig_pub_inputs =
        push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest, &macs, av_val);

    let hash_pub_inputs = (0..hash_public_bits.len())
        .map(|i| {
            crate::runtime::algebra::gf2_128::Gf2_128::from(u128::from(hash_public_bits.get(i)))
        })
        .collect::<Vec<_>>();
    let claims = super::mac_claims(&zk_spec.manifest, av_val, &macs, &gf2)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.hash_proof");
    let proof_hash = prover_hash
        .prove(
            &hash_pub_inputs,
            &claims,
            commit_hash,
            &mut tp,
            &context_hash,
        )
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.signature_proof");
    let proof_sig = prover_sig
        .prove(
            &sig_pub_inputs,
            witness_sig,
            commit_sig,
            &mut tp,
            &context_sig,
        )
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.prover.encoding_and_cleanup");
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
        .write(&geom, &gf2, &sf_hash, &p256, &sf_sig)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)
}
