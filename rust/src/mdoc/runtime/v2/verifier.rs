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
// Evaluation failures can expose private inputs; never write them to logs.
#![deny(clippy::print_stdout, clippy::print_stderr, clippy::dbg_macro)]

use crate::{
    mdoc::v2::{
        circuits::Instance,
        inputs::PublicInputs,
        request::{Request, RequestError},
        MdocVerifierErrorCode, RequestedAttribute, ZkSpecStruct,
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        v2::transcript::{Opened, VerifiedProof},
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
) -> Result<VerifiedProof, MdocVerifierErrorCode> {
    let p256 = P256Field::new();
    // Every later step takes the checked request; nothing is loaded before
    // the check passes.
    let request = Request::check(zk_spec, pkx, pky, transcript, attrs, now, doc_type, &p256)
        .map_err(request_error)?;
    let p256_2 = Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);

    let gf2 = Gf2_128Field::new();
    let make_interpolator_hash = BinaryInterpolatorFactory::full_field(&gf2);

    let instance = Instance::load(&request, circuits_compressed, &p256, &gf2)
        .map_err(|_| MdocVerifierErrorCode::CircuitParsingFailure)?;

    let gen_err = |_| MdocVerifierErrorCode::GeneralFailure;
    let composition = super::link::composition(
        request.spec(),
        instance.signature(),
        instance.hash(),
        (&make_interpolator_hash, &make_interpolator_sig),
    )
    .map_err(gen_err)?;
    let public = PublicInputs::derive(&request, &p256);
    let statement = super::transcript::MdocStatement::new(
        request.transcript(),
        request.spec(),
        composition
            .statement(public.hash(), public.signature())
            .map_err(gen_err)?,
    );
    let mut session = Opened::new(&statement);
    // The proof is parsed against the geometry the statement absorbed.
    let decoded =
        super::proto::MdocProof::read(proof_bytes, &session.bound(|s| &s.geometry), &gf2, &p256)
            .map_err(|_| MdocVerifierErrorCode::HashParsingFailure)?;
    let tp = super::link::Statement::verify(session, &decoded.body).map_err(gen_err)?;
    decoded
        .checked(tp)
        .map_err(|_| MdocVerifierErrorCode::GeneralFailure)
}

/// The verifier's codes for the request rows of the error table.
fn request_error(error: RequestError) -> MdocVerifierErrorCode {
    match error {
        RequestError::Version => MdocVerifierErrorCode::InvalidZkSpecVersion,
        RequestError::AttributeCount => MdocVerifierErrorCode::AttributeNumberMismatch,
        RequestError::Shape => MdocVerifierErrorCode::InvalidInput,
        RequestError::UnsupportedAttribute => MdocVerifierErrorCode::UnsupportedAttribute,
    }
}
