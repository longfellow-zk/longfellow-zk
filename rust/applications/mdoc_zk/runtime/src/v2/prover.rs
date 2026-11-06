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
    adapter::{transcript as adapter, BinaryParticipant, SharedParticipant},
    inputs::{
        public_inputs_fit, push_input_hash, push_input_sig, push_witness_hash, push_witness_sig,
    },
    ZkSpecStruct,
};
use crate::{
    core::algebra::SerializableField,
    mdoc::{
        circuits::cbor::mdoc::{parse_mdoc, MdocParseError, ParsedMdoc},
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
        v2::zk::ZkContext,
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

    let plan = crate::mdoc::circuits::p256_adapter::shared_plan();
    let mask = rng.elt_field(&p256);
    let mask_bytes = p256.to_bytes(&mask);
    let otp = rng.bytes(plan.advice_bytes());

    let mut tp = super::transcript::new(transcript, &zk_spec.combined_hash);
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
        parse_mdoc(mdoc_bytes, transcript, doc_type).map_err(|err| match err {
            MdocParseError::TooBig => MdocProverErrorCode::TaggedMsoTooBig,
            _ => MdocProverErrorCode::MsoDecodingFailure,
        })?;

    for req_attr in attrs {
        if parsed.get_attribute(&req_attr.id).is_none() {
            return Err(MdocProverErrorCode::AttributeNotFound);
        }
    }

    let mut witness_hash = push_witness_hash(attrs, &parsed)?;
    witness_hash.extend((0..256).map(|r| ((mask_bytes[r / 8] >> (r % 8)) & 1) != 0));
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;

    // Public presentation bits are fixed before the shared commitment.
    let app_public = push_input_hash(attrs, now.as_bytes(), false, doc_type.as_bytes());
    witness_hash.extend((0..plan.advice_bits()).map(|r| ((otp[r / 8] >> (r % 8)) & 1) != 0));
    let context_hash = ZkContext {
        f: &gf2,
        domain: &make_interpolator_hash,
    };
    let context_sig = ZkContext {
        f: &p256,
        domain: &make_interpolator_sig,
    };

    let prover_hash = BinaryParticipant::new(&c_hash, config_hash, &context_hash)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let prover_sig = SharedParticipant::new(
        &c_sig,
        crate::mdoc::circuits::p256_adapter::SHARED_BITS,
        config_sig,
        &context_sig,
    )
    .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let param = crate::runtime::v2::zk::joint::JointParam::new((
        prover_hash
            .participant(&context_hash)
            .map_err(|_| MdocProverErrorCode::GeneralFailure)?,
        (
            prover_sig
                .participant(&context_sig)
                .map_err(|_| MdocProverErrorCode::GeneralFailure)?,
            (),
        ),
    ))
    .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    super::transcript::bind_public_inputs(&mut tp, &app_public);
    prover_hash.bind(&mut tp);
    prover_sig.bind(&mut tp);
    let (state_hash, w_hash) = prover_hash
        .prepare(&witness_hash, rng)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let (state_sig, w_sig) = prover_sig
        .prepare(&c_sig, witness_sig, mask, rng, &p256)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let (joint, root, fingerprints) = param
        .commit((w_hash, (w_sig, ())), &mut tp, rng)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let sig_pub_inputs = push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest);
    let reduced = prover_sig
        .reduce(&c_sig, &sig_pub_inputs, state_sig, &mut tp, &p256)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let e = adapter::eta(&mut tp, &p256);
    let mu = reduced.masked_value(&e, &p256);
    let weights = adapter::weights(&reduced.claim.weights, &e, &mu, &mut tp, &p256)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let alpha = adapter::alphas(&mut tp, &p256);
    let mut values = reduced.values;
    values.push(reduced.mask);
    let encoded = plan
        .encode(&weights, &mu, &alpha, Some(&values), &p256, &gf2)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let q = encoded
        .quotients
        .ok_or(MdocProverErrorCode::GeneralFailure)?;
    let mut masked = vec![0; plan.advice_bytes()];
    for r in 0..plan.advice_bits() {
        let bit = ((q[r / plan.quotient_bits] >> (r % plan.quotient_bits)) as u8 & 1)
            ^ ((otp[r / 8] >> (r % 8)) & 1);
        masked[r / 8] |= bit << (r % 8);
    }
    let hash_pub_inputs = adapter::public(&plan, encoded, &masked, &mut tp)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let (proof_hash, statement_hash) = prover_hash
        .prove(
            &c_hash,
            &app_public,
            witness_hash,
            state_hash,
            &hash_pub_inputs,
            &mut tp,
            &context_hash,
        )
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let statement_sig = prover_sig
        .finish(reduced.claim, &e, &mu, &p256)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
    let proof_sig = crate::runtime::v2::proto::zk::CircuitProof {
        sumcheck_proof: reduced.proof,
        packing: crate::runtime::v2::proto::dual_packing::PackingProof::Direct,
    };
    let proof = joint
        .prove(&param, (statement_hash, (statement_sig, ())), &mut tp)
        .map_err(|_| MdocProverErrorCode::GeneralFailure)?;
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
    .map(|p| p.into_bytes())
    .map_err(|_| MdocProverErrorCode::GeneralFailure)
}
