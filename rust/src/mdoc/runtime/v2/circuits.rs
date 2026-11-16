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

//! Longfellow v2 circuit loading with mandatory payload ID verification.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::mdoc::v2::request::Request;
use crate::{
    core::proto::v2::{Circuit, CircuitReader},
    mdoc::v2::ZkSpecStruct,
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

type DecodedCircuits = (Circuit<P256Field>, Circuit<Gf2_128Field>);

/// Load circuits, validating their structure and recomputing their payload IDs.
pub fn decompress_circuits(
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
) -> Result<DecodedCircuits, String> {
    load(compressed, p256, gf2, None)
}

/// The circuits a checked request's spec names (DESIGN.md I3).
/// [`Instance::load`] is the only constructor.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) struct Instance {
    signature: Circuit<P256Field>,
    hash: Circuit<Gf2_128Field>,
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Instance {
    /// Check the archive's metadata against the request's spec, verify both
    /// payload identities, and check both circuits' public-input counts
    /// against the request.
    pub(super) fn load(
        request: &Request<'_>,
        compressed: &[u8],
        p256: &P256Field,
        gf2: &Gf2_128Field,
    ) -> Result<Self, String> {
        let (signature, hash) = load(compressed, p256, gf2, Some(request.spec()))?;
        // A is `spec.num_attributes`, which `Request::check` made equal to
        // the number of requested attributes.
        if Some(hash.raw.npublic_input) != hash_public_inputs(request.spec().num_attributes)
            || signature.raw.npublic_input != SIGNATURE_PUBLIC_INPUTS
        {
            return Err("Circuit public-input counts do not match the request".into());
        }
        Ok(Self { signature, hash })
    }
    pub(super) fn signature(&self) -> &Circuit<P256Field> {
        &self.signature
    }
    pub(super) fn hash(&self) -> &Circuit<Gf2_128Field> {
        &self.hash
    }
}

/// The hash circuit's public-input count for A attributes, `901 + 788 * A`
/// (DESIGN.md I3): the time (112), each attribute (788), then the
/// document-type flag, the document type and the namespace (789). None if it
/// overflows.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
fn hash_public_inputs(attributes: usize) -> Option<usize> {
    attributes.checked_mul(788)?.checked_add(901)
}

/// The signature circuit's public-input count (DESIGN.md I3): the issuer key
/// and the 256 bits of `e2`.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
const SIGNATURE_PUBLIC_INPUTS: usize = 258;

fn load(
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
    spec: Option<&ZkSpecStruct>,
) -> Result<DecodedCircuits, String> {
    let archive = super::archive::read(compressed)?;
    if archive.entries.len() != 2 {
        return Err("V2 archive must contain exactly the signature and hash circuits".into());
    }
    if let Some(expected) = spec {
        if archive.combined_id != expected.combined_hash
            || archive.circuit_version as usize != expected.version
        {
            return Err("Circuit archive does not match the selected v2 specification".into());
        }
    }
    let sig_entry = archive
        .get("sig")
        .ok_or("Missing 'sig' entry in circuit archive")?;
    let hash_entry = archive
        .get("hash")
        .ok_or("Missing 'hash' entry in circuit archive")?;
    let (signature, signature_tail) = CircuitReader::new(p256).from_bytes(&sig_entry.payload)?;
    if !signature_tail.is_empty() || signature.id != sig_entry.circuit_id {
        return Err("Signature payload does not match its archive entry".into());
    }
    let (hash, hash_tail) = CircuitReader::new(gf2).from_bytes(&hash_entry.payload)?;
    if !hash_tail.is_empty() || hash.id != hash_entry.circuit_id {
        return Err("Hash payload does not match its archive entry".into());
    }
    Ok((signature, hash))
}

#[cfg(test)]
mod tests;

/// Derive the application's proof codec dimensions from its trusted circuits.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub fn proof_geometry(
    spec: &ZkSpecStruct,
    signature: &Circuit<P256Field>,
    hash: &Circuit<Gf2_128Field>,
) -> Result<super::MdocProofGeometry, String> {
    super::domains::with_domains(&Gf2_128Field::new(), &P256Field::new(), |domains| {
        Ok(super::MdocProofGeometry {
            body: super::link::composition(spec, signature, hash, domains)?.geometry()?,
        })
    })
}
