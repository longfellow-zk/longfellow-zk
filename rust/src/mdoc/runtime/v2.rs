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

//! Longfellow v2 application API and its own specification registry.

pub(in crate::mdoc) mod archive;
mod attribute;
mod circuits;
#[cfg(any(test, feature = "prover"))]
mod document;
#[cfg(any(test, feature = "prover", feature = "verifier", feature = "compiler"))]
pub(in crate::mdoc) mod domains;
mod error;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod inputs;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod key;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod link;
mod proto;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod request;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
mod transcript;
mod zk_spec;
#[cfg(test)]
pub(in crate::mdoc::runtime) use attribute::{circuit_supports, same_namespace};
pub use attribute::{req_attr, RequestedAttribute};
pub use circuits::decompress_circuits;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use circuits::proof_geometry;
pub use error::{MdocProverErrorCode, MdocVerifierErrorCode};
#[cfg(feature = "testonly")]
pub use proto::proof_sizes;
#[cfg(test)]
pub(crate) use proto::MdocProof;
pub use proto::MdocProofGeometry;
pub use zk_spec::{
    find_zk_spec, find_zk_spec_by_hex, is_supported_version, ZkSpecStruct, MDOC_JOINT_PROFILE,
    NUM_ZK_SPECS, SUPPORTED_CIRCUIT_VERSIONS, SYSTEM_ID, ZK_SPECS,
};

pub mod provider;
cfg_prover! { mod prover; pub use prover::{run_mdoc_prover,run_mdoc_prover_inner}; #[cfg(test)] pub(in crate::mdoc::runtime) use prover::run_mdoc_prover_encoded; }
cfg_verifier! { mod verifier; pub use verifier::run_mdoc_verifier; }

/// Test hook: the reserved suffix start and the adapter fragment width of
/// mdoc's composition.
#[cfg(test)]
pub(crate) fn link_for_test<DH, DS>(
    spec: &ZkSpecStruct,
    signature: &crate::core::proto::v2::Circuit<crate::runtime::algebra::p256::P256Field>,
    hash: &crate::core::proto::v2::Circuit<crate::runtime::algebra::gf2_128::Gf2_128Field>,
    domains: (&DH, &DS),
) -> Result<(usize, usize), String>
where
    DH: crate::runtime::algebra::range_interpolation::EvaluationDomain<
        crate::runtime::algebra::gf2_128::Gf2_128Field,
    >,
    DS: crate::runtime::algebra::range_interpolation::EvaluationDomain<
        crate::runtime::algebra::p256::P256Field,
    >,
{
    use crate::runtime::v2::foreign::adapter::AdapterMode;
    let c = link::composition(spec, signature, hash, domains)?;
    Ok((c.reserved().start(), c.mode().fragment().raw.ninput))
}
