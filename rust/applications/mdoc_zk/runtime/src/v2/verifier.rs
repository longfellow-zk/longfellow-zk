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

    let gen_err = |_| MdocVerifierErrorCode::GeneralFailure;
    let composition = super::link::composition(
        zk_spec,
        &c_sig,
        &c_hash,
        (&make_interpolator_hash, &make_interpolator_sig),
    )
    .map_err(gen_err)?;
    let geometry = super::proto::MdocProofGeometry {
        body: composition.geometry().map_err(gen_err)?,
    };
    let decoded = super::proto::MdocProof::read(proof_bytes, &geometry, &gf2, &p256)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;

    let app_public = push_input_hash(attrs, now.as_bytes(), false, doc_type.as_bytes());
    let digest = crate::mdoc::circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = crate::runtime::algebra::RuntimeNat::<4>::from_bytes_be(&digest);
    let sig_public = push_input_sig(&p256, &issuer_pk, &e2_val);
    let mut tp = super::transcript::new(transcript, &zk_spec.combined_hash);
    super::transcript::absorb_public_inputs(&mut tp.borrow(), &app_public);
    let tp = composition
        .verify(&app_public, &sig_public, &decoded.body, tp)
        .map_err(gen_err)?;
    decoded
        .checked(tp)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)
}

pub use run_mdoc_verifier_inner as run_mdoc_verifier;
