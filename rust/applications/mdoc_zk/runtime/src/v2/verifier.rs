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

//! Shared-root mdoc verifier with a packed binary circuit and a prime P256 circuit.

use super::{
    inputs::{public_inputs_fit, push_input_hash, push_input_sig},
    ZkSpecStruct,
};
use crate::{
    core::algebra::Nat,
    mdoc::runtime::v2::{
        attribute::{circuit_supports, same_namespace},
        key::parse_pk_coordinate,
        MdocVerifierErrorCode, RequestedAttribute,
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        v2::{
            foreign::{self, mixed::MixedParticipant},
            zk::{joint::CircuitParticipant, ZkContext},
        },
    },
};

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
) -> Result<crate::runtime::v2::transcript::VerifiedProof, MdocVerifierErrorCode> {
    if !zk_spec.supports_version() {
        return Err(MdocVerifierErrorCode::InvalidZkSpecVersion);
    }
    if attrs.len() != zk_spec.num_attributes {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }
    let (config_hash, config_sig) = zk_spec.configs();
    if !same_namespace(attrs) {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }
    // Keep the established predicate-failure code, but reject before loading
    // circuits or parsing an otherwise irrelevant proof.
    if doc_type.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }
    if !public_inputs_fit(attrs, now.as_bytes(), doc_type.as_bytes()) {
        return Err(MdocVerifierErrorCode::InvalidInput);
    }
    for a in attrs {
        if !circuit_supports(&a.cbor_value) {
            return Err(MdocVerifierErrorCode::UnsupportedAttribute);
        }
    }

    let p256 = P256Field::new();
    let issuer_pk = (
        parse_pk_coordinate(pkx, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?,
        parse_pk_coordinate(pky, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?,
    );
    let p256_2 = crate::runtime::algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let gf2 = Gf2_128Field::new();
    let make_interpolator_hash = BinaryInterpolatorFactory::full_field(&gf2);

    let (c_sig, c_hash) = super::circuits::for_spec(zk_spec, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;

    let context_hash = ZkContext::new(&make_interpolator_hash);
    let context_sig = ZkContext::new(&make_interpolator_sig);
    let gen_err = |_| MdocVerifierErrorCode::GeneralFailure;

    let link = super::link::Link::new(&c_hash).map_err(gen_err)?;
    let storage = link.storage(&c_sig).map_err(gen_err)?;
    let verifier_hash = CircuitParticipant::with_virtual_inputs(
        &c_hash,
        &[&link.fragment],
        link.virtual_inputs(),
        config_hash,
        &context_hash,
    )
    .map_err(gen_err)?;
    let verifier_sig = MixedParticipant::new(&c_sig, storage, link.mask, config_sig, &context_sig)
        .map_err(gen_err)?;
    let param = crate::runtime::v2::zk::joint::JointParam::new((
        verifier_hash.participant(&context_hash).map_err(gen_err)?,
        (verifier_sig.participant(&context_sig).map_err(gen_err)?, ()),
    ))
    .map_err(gen_err)?;
    let geom = super::proto::MdocProofGeometry {
        geom_hash: verifier_hash.geometry(),
        geom_sig: verifier_sig.geometry(),
        joint_context: param.context(),
        config: param.config(),
    };
    let decoded = super::proto::MdocProof::read(proof_bytes, &geom, &gf2, &p256)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;
    let super::proto::MdocProof {
        commitment: root,
        fingerprints,
        mu,
        masked,
        proof_hash,
        proof_sig,
        polygero: proof,
    } = &*decoded;
    let mut tp = super::transcript::new(transcript, &zk_spec.combined_hash);

    let app_public = push_input_hash(attrs, now.as_bytes(), false, doc_type.as_bytes());
    super::transcript::absorb_public_inputs(&mut tp.borrow(), &app_public);
    let mut joint = param.receive(root, fingerprints.clone(), tp);
    let mut tp = joint.transcript();

    // Signature frontend, then the mixed split of its batched claim.
    let digest = crate::mdoc::circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = crate::runtime::algebra::RuntimeNat::<4>::from_bytes_be(&digest);
    let pub_inputs_sig = push_input_sig(&p256, &issuer_pk, &e2_val);
    let claim = verifier_sig
        .reduce(
            &c_sig,
            &pub_inputs_sig,
            &proof_sig.sumcheck_proof,
            &mut tp,
            &p256,
        )
        .map_err(gen_err)?;
    let eta = foreign::transcript::eta(&mut tp, &p256);
    foreign::transcript::absorb_mu(&mut tp, mu, &p256);
    let link_claim = verifier_sig
        .foreign_claim(&claim, &eta, mu, &p256)
        .map_err(gen_err)?;

    // Adapter: conversion challenges, then the published masked words.
    let alpha = foreign::adapter::p256::conversion(&mut tp, &p256);
    let encoded = link
        .plan
        .encode(&link_claim, &alpha, None, &p256, &gf2)
        .map_err(gen_err)?;
    foreign::adapter::p256::absorb_masked(&mut tp, masked);
    let leaves = foreign::adapter::virtual_inputs(
        link.shape,
        encoded.trees(&link_claim, &link.otp, masked, &gf2),
        &gf2,
    )
    .map_err(gen_err)?;

    // Binary frontend: hash circuit and the fixed adapter fragment.
    let statement_hash = verifier_hash
        .reduce_virtual(
            &c_hash,
            &app_public,
            proof_hash,
            &[&link.fragment],
            &leaves,
            &mut tp,
            &context_hash,
        )
        .map_err(gen_err)?;
    let statement_sig = verifier_sig
        .native_statement(&claim, &eta, mu, &p256)
        .map_err(gen_err)?;
    let tp = joint
        .authenticate(proof, (statement_hash, (statement_sig, ())))
        .map_err(gen_err)?
        .into_transcript();
    decoded
        .checked(tp)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)
}

pub use run_mdoc_verifier_inner as run_mdoc_verifier;
