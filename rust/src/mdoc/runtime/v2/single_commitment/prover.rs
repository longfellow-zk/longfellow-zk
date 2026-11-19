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

//! One binary commitment authenticates the scalar hash and P256 frontends.
// Evaluation failures can expose private inputs; never write them to logs.
#![deny(clippy::print_stdout, clippy::print_stderr, clippy::dbg_macro)]

use super::encoding::SignatureEncoding;
use crate::{
    mdoc::{
        cbor::mdoc::{MdocParseError, ParsedMdoc},
        v2::{
            circuits::Instance,
            inputs::{push_witness_hash, push_witness_sig, PublicInputs},
            request::{Request, RequestError},
            MdocProverErrorCode, RequestedAttribute, ZkSpecStruct,
        },
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            q256::Q256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            secp256r1::Secp256r1,
            RuntimeNat, SupportsFFT,
        },
        random::{PrivateRandom, SecureRandomEngine},
        v2::transcript::{EncodedProof, Opened},
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
    let mut rng = SecureRandomEngine::new();
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
pub fn run_mdoc_prover_inner<RNG: PrivateRandom>(
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
pub(in crate::mdoc::runtime) fn run_mdoc_prover_encoded<RNG: PrivateRandom>(
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
) -> Result<EncodedProof, MdocProverErrorCode> {
    run_mdoc_prover_encoded_with_encoding(
        zk_spec,
        circuits_compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        SignatureEncoding::default(),
        rng,
    )
}

/// Prove with an explicit, transcript-bound signature representation.
#[allow(clippy::too_many_arguments)]
pub fn run_mdoc_prover_inner_with_encoding<RNG: PrivateRandom>(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    encoding: SignatureEncoding,
    rng: &mut RNG,
) -> Result<Vec<u8>, MdocProverErrorCode> {
    run_mdoc_prover_encoded_with_encoding(
        zk_spec,
        circuits_compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        attrs,
        now,
        doc_type,
        encoding,
        rng,
    )
    .map(|proof| proof.into_bytes())
}

#[allow(clippy::too_many_arguments)]
fn run_mdoc_prover_encoded_with_encoding<RNG: PrivateRandom>(
    zk_spec: &ZkSpecStruct,
    circuits_compressed: &[u8],
    mdoc_bytes: &[u8],
    pkx: &str,
    pky: &str,
    transcript: &[u8],
    attrs: &[RequestedAttribute],
    now: &str,
    doc_type: &str,
    encoding: SignatureEncoding,
    rng: &mut RNG,
) -> Result<EncodedProof, MdocProverErrorCode> {
    let p256 = P256Field::new();
    let request = Request::check(zk_spec, pkx, pky, transcript, attrs, now, doc_type, &p256)
        .map_err(|error| match error {
            RequestError::Version => MdocProverErrorCode::InvalidZkSpecVersion,
            RequestError::AttributeCount | RequestError::Shape => MdocProverErrorCode::InvalidInput,
            RequestError::UnsupportedAttribute => MdocProverErrorCode::UnsupportedAttribute,
        })?;
    let p256_2 = Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let q256 = Q256Field::new();
    let secp256r1 = Secp256r1::new(&p256);

    let gf2 = Gf2_128Field::new();
    let make_interpolator_hash = BinaryInterpolatorFactory::full_field(&gf2);

    let instance = Instance::load(&request, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocProverErrorCode::CircuitParsingFailure)?;

    let parsed: ParsedMdoc<RuntimeNat<4>> =
        super::super::document::parse(mdoc_bytes, &request, &p256).map_err(|err| {
            match err {
                super::super::document::Error::Encoding(MdocParseError::TooBig) => {
                    MdocProverErrorCode::TaggedMsoTooBig
                }
                super::super::document::Error::Encoding(_)
                | super::super::document::Error::TooLong => MdocProverErrorCode::MsoDecodingFailure,
                // Preserve the circuit's existing rejection code for well-formed
                // documents that fail a presentation predicate.
                super::super::document::Error::Predicate => MdocProverErrorCode::GeneralFailure,
            }
        })?;

    let gen_err = |_| MdocProverErrorCode::GeneralFailure;
    let composition = super::link::Link::with_encoding(
        zk_spec,
        instance.signature(),
        instance.hash(),
        (&make_interpolator_hash, &make_interpolator_sig),
        encoding,
    )
    .map_err(gen_err)?;
    let witness_hash = push_witness_hash(&request, &parsed)?;
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &request, &parsed)?;
    let public = PublicInputs::derive(&request, &p256);

    // Public presentation bits are fixed before the shared commitment.
    let statement = composition.statement(&public).map_err(gen_err)?;
    let (body, completed) = composition
        .prove(witness_hash, witness_sig, Opened::new(&statement), rng)
        .map_err(gen_err)?;
    let geometry = composition.geometry().map_err(gen_err)?;
    body.write(&geometry, &gf2, &p256, completed)
        .map_err(gen_err)
}
