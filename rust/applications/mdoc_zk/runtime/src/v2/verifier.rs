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

//! Longfellow v2 application verifier.

pub use run_mdoc_verifier_inner as run_mdoc_verifier;

use super::{
    inputs::{public_inputs_fit, push_input_hash, push_input_sig},
    proto::{MdocProof, MdocProofGeometry},
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
        polygero::{JointPolygeroParam, JointPolygeroVerifier},
        random::{transcript::Transcript, RandomEngine},
        zk_v2::{joint::CircuitParticipant, ZkContext},
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
) -> Result<(), MdocVerifierErrorCode> {
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

    let context_hash = ZkContext {
        f: &gf2,
        domain: &make_interpolator_hash,
    };
    let context_sig = ZkContext {
        f: &p256,
        domain: &make_interpolator_sig,
    };
    let verifier_hash = CircuitParticipant::new(&c_hash, config_hash, &context_hash)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let verifier_sig = CircuitParticipant::new(&c_sig, config_sig, &context_sig)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let joint = JointPolygeroParam::new((
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
    let geom = MdocProofGeometry {
        geom_hash: verifier_hash.geometry(),
        geom_sig: verifier_sig.geometry(),
        joint_context: joint.context(),
        config: joint.config(),
    };
    let (remaining, proof) = MdocProof::read(proof_bytes, &geom, &gf2, &p256)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;

    if !remaining.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }

    let mut tp = Transcript::new(transcript);

    verifier_hash.bind(&mut tp);
    verifier_sig.bind(&mut tp);
    let mut polygero = JointPolygeroVerifier::new(joint);
    // Fix both fields before the MAC challenge, using the same root and order
    // as the prover. Circuit verification below only reconstructs constraints.
    polygero.receive_commitment(&proof.commitment, &mut tp);

    let av_val = tp.u128();

    let pub_inputs_hash = push_input_hash(
        attrs,
        now.as_bytes(),
        &proof.macs,
        av_val,
        false,
        doc_type.as_bytes(),
    );

    if pub_inputs_hash.len() != c_hash.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    let statement_hash = verifier_hash
        .verify(
            &c_hash,
            &pub_inputs_hash,
            &proof.proof_hash,
            &mut tp,
            &context_hash,
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    let digest = crate::mdoc::circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = crate::runtime::algebra::RuntimeNat::<4>::from_bytes_be(&digest);

    let pub_inputs_sig = push_input_sig(&p256, &issuer_pk, &e2_val, &proof.macs, av_val);

    if pub_inputs_sig.len() != c_sig.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    let statement_sig = verifier_sig
        .verify(
            &c_sig,
            &pub_inputs_sig,
            &proof.proof_sig,
            &mut tp,
            &context_sig,
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    // Acceptance requires both reconstructed statements to pass against the
    // shared authenticated columns; neither circuit reduction suffices alone.
    polygero
        .verify(
            &proof.commitment,
            &proof.polygero,
            &(statement_hash, (statement_sig, ())),
            &mut tp,
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    Ok(())
}
