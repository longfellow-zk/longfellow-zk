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

//! Longfellow v1 application verifier.

use super::{
    inputs::{push_input_hash, push_input_sig},
    proto::{MdocProof, MdocProofGeometry},
    ZkSpecStruct,
};
use crate::{
    core::algebra::Nat,
    mdoc::runtime::v1::{
        attribute::same_namespace, key::parse_pk_coordinate, MdocVerifierErrorCode,
        RequestedAttribute,
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
        zk_v1::ZkVerifier,
    },
};

#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_verifier(
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
    run_mdoc_verifier_inner(
        zk_spec,
        circuits_compressed,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        proof_bytes,
    )
}

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
    let version = zk_spec.version;
    if !zk_spec.is_valid() {
        return Err(MdocVerifierErrorCode::InvalidZkSpecVersion);
    }
    let (config_hash, config_sig) = super::ligero_configs(zk_spec);
    if !same_namespace(attrs) {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }
    // Legacy circuits bind doc_type through the DeviceAuthentication /
    // COSE_Sign1 transcript hash (e2_val); v8 checks it directly in the circuit.

    let p256 = P256Field::new();
    let p256_2 = crate::runtime::algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let gf2 = Gf2_128Field::new();
    let sf_hash = crate::runtime::algebra::subfield_v1::BinarySubfield::new(
        &crate::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator_hash = BinaryInterpolatorFactory::new(&gf2, &sf_hash);

    let (c_sig, c_hash) = super::circuits::decompress_circuits(circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;

    let verifier_hash = ZkVerifier::<2, _>::new(c_hash, config_hash);
    let geom_hash = verifier_hash.geometry(&crate::runtime::zk_v1::common::ZkContext {
        f: &gf2,
        make_interpolator: &make_interpolator_hash,
    });

    let verifier_sig = ZkVerifier::<4, _>::new(c_sig, config_sig);
    let geom_sig = verifier_sig.geometry(&crate::runtime::zk_v1::common::ZkContext {
        f: &p256,
        make_interpolator: &make_interpolator_sig,
    });

    let geom = MdocProofGeometry {
        geom_hash,
        geom_sig,
    };

    let sf_sig = crate::runtime::algebra::p256::P256Subfield::new(&p256);
    let (remaining, proof) = MdocProof::read(proof_bytes, &geom, &gf2, &sf_hash, &p256, &sf_sig)
        .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;

    if !remaining.is_empty() {
        return Err(MdocVerifierErrorCode::GeneralFailure);
    }

    let mut tp = Transcript::new(transcript);

    verifier_hash.recv_commitment(
        &proof.proof_hash,
        &mut tp,
        &crate::runtime::zk_v1::common::ZkContext {
            f: &gf2,
            make_interpolator: &make_interpolator_hash,
        },
    );
    verifier_sig.recv_commitment(
        &proof.proof_sig,
        &mut tp,
        &crate::runtime::zk_v1::common::ZkContext {
            f: &p256,
            make_interpolator: &make_interpolator_sig,
        },
    );

    let av_buf = tp.bytes(16);
    let av_val = u128::from_le_bytes(av_buf.try_into().unwrap());

    let pub_inputs_hash =
        push_input_hash(version, &gf2, attrs, now.as_bytes(), &proof.macs, av_val);

    if pub_inputs_hash.len() != verifier_hash.circuit.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    verifier_hash
        .verify(
            pub_inputs_hash,
            &proof.proof_hash,
            &mut tp,
            &crate::runtime::zk_v1::common::ZkContext {
                f: &gf2,
                make_interpolator: &make_interpolator_hash,
            },
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    let pk_x_elt =
        parse_pk_coordinate(pkx, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?;
    let pk_y_elt =
        parse_pk_coordinate(pky, &p256).map_err(|_| MdocVerifierErrorCode::InvalidInput)?;

    let digest = crate::mdoc::circuits::cbor::mdoc::compute_transcript_hash(transcript, doc_type);
    let e2_val = crate::runtime::algebra::RuntimeNat::<4>::from_bytes_be(&digest);

    let pub_inputs_sig = push_input_sig(&p256, &(pk_x_elt, pk_y_elt), &e2_val, &proof.macs, av_val);

    if pub_inputs_sig.len() != verifier_sig.circuit.raw.npublic_input {
        return Err(MdocVerifierErrorCode::AttributeNumberMismatch);
    }

    verifier_sig
        .verify(
            pub_inputs_sig,
            &proof.proof_sig,
            &mut tp,
            &crate::runtime::zk_v1::common::ZkContext {
                f: &p256,
                make_interpolator: &make_interpolator_sig,
            },
        )
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)?;

    Ok(())
}
