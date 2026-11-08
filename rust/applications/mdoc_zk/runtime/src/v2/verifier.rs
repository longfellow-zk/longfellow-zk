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
    adapter::{transcript as adapter, BinaryParticipant, SharedParticipant},
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
        v2::zk::ZkContext,
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

    let plan = crate::mdoc::circuits::p256_adapter::shared_plan();
    let verifier_hash = BinaryParticipant::new(&c_hash, config_hash, &context_hash)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let verifier_sig = SharedParticipant::new(
        &c_sig,
        crate::mdoc::circuits::p256_adapter::SHARED_BITS,
        config_sig,
        &context_sig,
    )
    .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let param = crate::runtime::v2::zk::joint::JointParam::new((
        verifier_hash
            .participant(&context_hash)
            .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?,
        (
            verifier_sig
                .participant(&context_sig)
                .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?,
            (),
        ),
    ))
    .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let geom = super::proto::MdocProofGeometry {
        geom_hash: verifier_hash.geometry(),
        geom_sig: verifier_sig.geometry(),
        joint_context: param.context(),
        config: param.config(),
    };
    let (remaining, decoded) = super::proto::MdocProof::read(proof_bytes, &geom, &gf2, &p256)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;
    if !remaining.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }
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
    super::transcript::bind_public_inputs(&mut tp.borrow(), &app_public);
    verifier_hash.bind(&mut tp.borrow());
    verifier_sig.bind(&mut tp.borrow());
    let mut joint = param.receive(root, fingerprints.clone(), tp);
    let mut tp = joint.transcript();
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
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let e = adapter::eta(&mut tp, &p256);
    let weights = adapter::weights(&claim.weights, &e, mu, &mut tp, &p256)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let alpha = adapter::alphas(&mut tp, &p256);
    let encoded = plan
        .encode(&weights, mu, &alpha, None, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let pub_inputs_hash = adapter::public(&plan, encoded, masked, &mut tp)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let statement_hash = verifier_hash
        .reduce(
            &c_hash,
            &app_public,
            proof_hash,
            &pub_inputs_hash,
            &mut tp,
            &context_hash,
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let statement_sig = verifier_sig
        .finish(claim, &e, mu, &p256)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let tp = joint
        .authenticate(proof, (statement_hash, (statement_sig, ())))
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?
        .into_transcript();
    decoded
        .checked(tp)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)
}

pub use run_mdoc_verifier_inner as run_mdoc_verifier;
