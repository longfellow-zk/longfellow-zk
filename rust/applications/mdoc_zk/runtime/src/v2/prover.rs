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

//! Shared-root mdoc prover with a packed binary circuit and a prime P256 circuit.

use super::{
    link,
    inputs::{
        public_inputs_fit, push_input_hash, push_input_sig, push_witness_hash, push_witness_sig,
    },
    ZkSpecStruct,
};
use crate::{
    core::algebra::SerializableField,
    mdoc::{
        circuits::cbor::mdoc::{MdocParseError, ParsedMdoc},
        runtime::v2::{
            attribute::{circuit_supports, same_namespace},
            key::parse_pk_coordinate,
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
        random::RandomEngine,
        v2::{
            foreign::{
                self,
                mixed::MixedParticipant,
                word::{MaskedWord, Otp},
            },
            zk::{joint::CircuitParticipant, ZkContext},
        },
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
    run_mdoc_prover_encoded(
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
    .map(|proof| proof.into_bytes())
}

#[allow(clippy::too_many_arguments)]
pub(in crate::mdoc::runtime) fn run_mdoc_prover_encoded<RNG: RandomEngine>(
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
) -> Result<crate::runtime::v2::transcript::EncodedProof, MdocProverErrorCode> {
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

    let p256_2 = crate::runtime::algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let q256 = crate::runtime::algebra::Q256Field::new();
    let secp256r1 = Secp256r1::new(&p256);

    let gf2 = Gf2_128Field::new();
    let make_interpolator_hash = BinaryInterpolatorFactory::full_field(&gf2);

    let (c_sig, c_hash) = super::circuits::for_spec(zk_spec, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;

    let parsed: ParsedMdoc<crate::runtime::algebra::RuntimeNat<4>> =
        super::document::parse(mdoc_bytes, transcript, doc_type, now, &p256).map_err(|err| {
            match err {
                super::document::Error::Encoding(MdocParseError::TooBig) => {
                    MdocProverErrorCode::TaggedMsoTooBig
                }
                super::document::Error::Encoding(_) => MdocProverErrorCode::MsoDecodingFailure,
                // Preserve the circuit's existing rejection code for well-formed
                // documents that fail a presentation predicate.
                super::document::Error::Predicate => MdocProverErrorCode::GeneralFailure,
            }
        })?;

    let gen_err = |_| MdocProverErrorCode::GeneralFailure;
    let link = super::link::Link::new(&c_hash).map_err(gen_err)?;
    let storage = link.storage(&c_sig).map_err(gen_err)?;

    let mask = rng.elt_field(&p256);
    let mask_bytes = p256.to_bytes(&mask);
    let otp = [Otp::<{ link::Q }>::sample(rng), Otp::sample(rng)];

    let mut tp = super::transcript::new(transcript, &zk_spec.combined_hash);

    // Hash witness, then the reserved suffix written by typed position.
    let mut witness_hash = push_witness_hash(attrs, &parsed)?;
    let mut reserved = link.suffix.witness();
    reserved
        .set(
            link.mask,
            (0..256).map(|r| ((mask_bytes[r / 8] >> (r % 8)) & 1) != 0),
        )
        .map_err(gen_err)?;
    for (group, pad) in link.otp.iter().zip(&otp) {
        reserved.set(group.group(), pad.bits()).map_err(gen_err)?;
    }
    witness_hash.extend(reserved.into_bits());
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed)
        .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;

    // Public presentation bits are fixed before the shared commitment.
    let app_public = push_input_hash(attrs, now.as_bytes(), false, doc_type.as_bytes());
    let context_hash = ZkContext::new(&make_interpolator_hash);
    let context_sig = ZkContext::new(&make_interpolator_sig);

    let prover_hash = CircuitParticipant::with_virtual_inputs(
        &c_hash,
        &[&link.fragment],
        link.virtual_inputs(),
        config_hash,
        &context_hash,
    )
    .map_err(gen_err)?;
    let prover_sig = MixedParticipant::new(&c_sig, storage, link.mask, config_sig, &context_sig)
        .map_err(gen_err)?;
    let param = crate::runtime::v2::zk::joint::JointParam::new((
        prover_hash.participant(&context_hash).map_err(gen_err)?,
        (prover_sig.participant(&context_sig).map_err(gen_err)?, ()),
    ))
    .map_err(gen_err)?;
    super::transcript::absorb_public_inputs(&mut tp.borrow(), &app_public);
    let (state_hash, w_hash) = prover_hash.prepare(witness_hash, rng).map_err(gen_err)?;
    let (state_sig, w_sig) = prover_sig
        .prepare(&c_sig, witness_sig, mask, rng, &p256)
        .map_err(gen_err)?;
    let (mut joint, root, fingerprints) = param
        .commit((w_hash, (w_sig, ())), tp, rng)
        .map_err(gen_err)?;
    let mut tp = joint.transcript();

    // Signature frontend, then the mixed split of its batched claim.
    let sig_pub_inputs = push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest);
    let reduced = prover_sig
        .prove(&c_sig, &sig_pub_inputs, state_sig, &mut tp, &p256)
        .map_err(gen_err)?;
    let eta = foreign::transcript::eta(&mut tp, &p256);
    let mu = reduced.masked_value(&prover_sig, &eta, &p256);
    foreign::transcript::absorb_mu(&mut tp, &mu, &p256);
    let claim = prover_sig
        .foreign_claim(&reduced.claim, &eta, &mu, &p256)
        .map_err(gen_err)?;

    // Adapter: conversion challenges, honest quotients, masked words.
    let alpha = foreign::adapter::p256::conversion(&mut tp, &p256);
    let values = reduced.foreign_values(&prover_sig);
    let encoded = link
        .plan
        .encode(&claim, &alpha, Some(&values), &p256, &gf2)
        .map_err(gen_err)?;
    let quotients = encoded.quotients.ok_or(MdocProverErrorCode::GeneralFailure)?;
    let masked = [
        MaskedWord::mask(quotients[0], &otp[0]),
        MaskedWord::mask(quotients[1], &otp[1]),
    ];
    foreign::adapter::p256::absorb_masked(&mut tp, &masked);
    let leaves = foreign::adapter::virtual_inputs(
        link.shape,
        encoded.trees(&claim, &link.otp, &masked, &gf2),
        &gf2,
    )
    .map_err(gen_err)?;

    // Binary frontend: hash circuit and the fixed adapter fragment.
    let (proof_hash, statement_hash) = prover_hash
        .prove_virtual(
            &c_hash,
            &app_public,
            state_hash,
            &[&link.fragment],
            &leaves,
            &mut tp,
            &context_hash,
        )
        .map_err(gen_err)?;
    let statement_sig = prover_sig
        .native_statement(&reduced.claim, &eta, &mu, &p256)
        .map_err(gen_err)?;
    let proof_sig = crate::runtime::v2::proto::zk::CircuitProof {
        sumcheck_proof: reduced.proof,
        packing: crate::runtime::v2::proto::dual_packing::PackingProof::Direct,
    };
    let (proof, tp) = joint
        .prove(&param, (statement_hash, (statement_sig, ())))
        .map_err(gen_err)?;
    super::proto::MdocProof {
        commitment: root,
        fingerprints,
        mu,
        masked,
        proof_hash,
        proof_sig,
        polygero: proof,
    }
    .write(
        &super::proto::MdocProofGeometry {
            geom_hash: prover_hash.geometry(),
            geom_sig: prover_sig.geometry(),
            joint_context: param.context(),
            config: param.config(),
        },
        &gf2,
        &p256,
        tp,
    )
    .map_err(gen_err)
}
