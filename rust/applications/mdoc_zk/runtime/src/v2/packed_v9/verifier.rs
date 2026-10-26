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

//! Experimental packed-v9 application verifier with a direct-field signature proof.

pub use run_mdoc_verifier_inner as run_mdoc_verifier;

use super::{
    super::inputs::{public_inputs_fit, push_input_hash_packed, push_input_sig},
    proto::{MdocProof, MdocProofGeometry},
    PackedV9Spec,
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
        random::{transcript::Transcript, RandomEngine},
        zk_v2::{ZkContext, ZkVerifier},
    },
};

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_verifier_inner(
    zk_spec: &PackedV9Spec,
    circuits_compressed: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    proof_bytes: &[u8],
) -> Result<(), MdocVerifierErrorCode> {
    #[cfg(feature = "bench-profile")]
    let mut profile = crate::util::profile::Timer::new("app.verifier.setup");
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
    let sf_hash = crate::runtime::algebra::subfield::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator_hash = BinaryInterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = super::provider::load_trusted(zk_spec, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;

    let context_hash = ZkContext {
        f: &gf2,
        domain: &make_interpolator_hash,
    };
    let context_sig = ZkContext {
        f: &p256,
        domain: &make_interpolator_sig,
    };

    let sf_sig = crate::runtime::algebra::p256::P256Subfield::new(&p256);
    let hash_protocol = crate::runtime::zk_v2::packed::PackedCircuit::new(
        c_hash,
        config_hash,
        6,
        zk_spec.manifest.digest(),
    )
    .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;
    let public_hash_count = hash_protocol.public_input_count();
    let mut verifier_hash =
        crate::runtime::zk_v2::packed::PackedVerifier::new(hash_protocol, &context_hash)
            .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let geom_hash = verifier_hash.geometry();

    let mut verifier_sig = ZkVerifier::<4, _>::new(c_sig, config_sig, &context_sig)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    let geom_sig = verifier_sig.geometry();

    let geom = MdocProofGeometry {
        geom_hash,
        geom_sig,
    };

    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.proof_decoding");
    let (remaining, proof) = MdocProof::read(proof_bytes, &geom, &gf2, &sf_hash, &p256, &sf_sig)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;

    if !remaining.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }

    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.public_statement");
    let mut tp = Transcript::new(transcript);

    verifier_hash.receive_commitment(&proof.proof_hash, &mut tp);
    verifier_sig.receive_commitment(&proof.proof_sig, &mut tp);

    let av_val = tp.u128();

    let hash_public_bits = push_input_hash_packed(
        &gf2,
        attrs,
        now.as_bytes(),
        false,
        doc_type.as_bytes(),
    );

    if hash_public_bits.len() != public_hash_count {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    let pub_inputs_hash = (0..hash_public_bits.len())
        .map(|i| {
            crate::runtime::algebra::gf2_128::Gf2_128::from(u128::from(hash_public_bits.get(i)))
        })
        .collect::<Vec<_>>();
    let claims = super::mac_claims(&zk_spec.manifest, av_val, &proof.macs, &gf2)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;
    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.hash_proof");
    verifier_hash
        .verify(
            &pub_inputs_hash,
            &claims,
            &proof.proof_hash,
            &mut tp,
            &context_hash,
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.signature_inputs");
    let digest = crate::mdoc::circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = crate::runtime::algebra::RuntimeNat::<4>::from_bytes_be(&digest);

    let pub_inputs_sig = push_input_sig(&p256, &issuer_pk, &e2_val, &proof.macs, av_val);

    if pub_inputs_sig.len() != verifier_sig.public_input_count() {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.signature_proof");
    verifier_sig
        .verify(&pub_inputs_sig, &proof.proof_sig, &mut tp, &context_sig)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    #[cfg(feature = "bench-profile")]
    profile.next("app.verifier.cleanup");
    Ok(())
}
