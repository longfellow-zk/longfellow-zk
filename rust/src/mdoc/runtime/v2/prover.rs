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
// Evaluation failures can expose private inputs; never write them to logs.
#![deny(clippy::print_stdout, clippy::print_stderr, clippy::dbg_macro)]

use crate::{
    mdoc::{
        circuits::cbor::mdoc::{MdocParseError, ParsedMdoc},
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
    let p256 = P256Field::new();
    // Every later step takes the checked request; nothing is loaded and no
    // randomness is drawn before the check passes.
    let request = Request::check(zk_spec, pkx, pky, transcript, attrs, now, doc_type, &p256)
        .map_err(request_error)?;

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

    let parsed: ParsedMdoc<RuntimeNat<4>> = super::document::parse(mdoc_bytes, &request, &p256)
        .map_err(|err| {
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
        request.spec(),
        instance.signature(),
        instance.hash(),
        (&make_interpolator_hash, &make_interpolator_sig),
    )
    .map_err(gen_err)?;
    let witness_hash = push_witness_hash(&request, &parsed)?;
    let witness_sig = push_witness_sig(&p256, &q256, &secp256r1, &request, &parsed)
        .map_err(|_| MdocProverErrorCode::WitnessCreationFailure)?;
    let public = PublicInputs::derive(&request, &p256);

    // The statement fixes the spec, the circuits, the geometry and every
    // public input before the shared commitment (transcript I1).
    let statement = super::transcript::MdocStatement::new(
        request.transcript(),
        request.spec(),
        composition
            .statement(public.hash(), public.signature())
            .map_err(gen_err)?,
    );
    let (body, tp) =
        super::link::Statement::prove(Opened::new(&statement), witness_hash, witness_sig, rng)
            .map_err(gen_err)?;
    super::proto::MdocProof { body }
        .write(&statement.geometry, &gf2, &p256, tp)
        .map_err(gen_err)
}

/// The prover's codes for the request rows of the error table: the attribute
/// count is an ordinary input error, since this enum has no count code.
fn request_error(error: RequestError) -> MdocProverErrorCode {
    match error {
        RequestError::Version => MdocProverErrorCode::InvalidZkSpecVersion,
        RequestError::AttributeCount | RequestError::Shape => MdocProverErrorCode::InvalidInput,
        RequestError::UnsupportedAttribute => MdocProverErrorCode::UnsupportedAttribute,
    }
}
