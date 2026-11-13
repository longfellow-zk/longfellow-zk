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
    inputs::{
        public_inputs_fit, push_input_hash, push_input_sig, push_witness_hash, push_witness_sig,
    },
    ZkSpecStruct,
};
use crate::{
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
    let composition = super::link::composition(
        zk_spec,
        &c_sig,
        &c_hash,
        (&make_interpolator_hash, &make_interpolator_sig),
    )
    .map_err(gen_err)?;
    let witness_hash = push_witness_hash(attrs, &parsed)?;
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &issuer_pk, &parsed)
        .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;
    let app_public = push_input_hash(attrs, now.as_bytes(), false, doc_type.as_bytes());
    let sig_public = push_input_sig(&p256, &issuer_pk, &parsed.device_sig_digest);

    // Public presentation bits are fixed before the shared commitment.
    let mut tp = super::transcript::new(transcript, &zk_spec.combined_hash);
    super::transcript::absorb_public_inputs(&mut tp.borrow(), &app_public);
    let (body, tp) = composition
        .prove(&app_public, witness_hash, &sig_public, witness_sig, tp, rng)
        .map_err(gen_err)?;
    let geometry = super::MdocProofGeometry {
        body: composition.geometry().map_err(gen_err)?,
    };
    super::proto::MdocProof { body }
        .write(&geometry, &gf2, &p256, tp)
        .map_err(gen_err)
}
