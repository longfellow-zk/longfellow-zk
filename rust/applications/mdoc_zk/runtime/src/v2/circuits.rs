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
use super::ZkSpecStruct;
use crate::{
    core::proto::{
        v2::{Circuit, CircuitReader},
        FieldID,
    },
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

/// Check archive metadata against the spec and verify both payload identities.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn for_spec(
    spec: &ZkSpecStruct,
    compressed: &[u8],
    p256: &P256Field,
    gf2: &Gf2_128Field,
) -> Result<DecodedCircuits, String> {
    load(compressed, p256, gf2, Some(spec))
}

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
    let (signature, signature_tail) =
        CircuitReader::new(p256, FieldID::P256).from_bytes(&sig_entry.payload)?;
    if !signature_tail.is_empty() || signature.id != sig_entry.circuit_id {
        return Err("Signature payload does not match its archive entry".into());
    }
    let (hash, hash_tail) =
        CircuitReader::new(gf2, FieldID::Gf2_128).from_bytes(&hash_entry.payload)?;
    if !hash_tail.is_empty() || hash.id != hash_entry.circuit_id {
        return Err("Hash payload does not match its archive entry".into());
    }
    Ok((signature, hash))
}

#[cfg(test)]
#[path = "../../tests/v2_circuits.rs"]
mod tests;

/// Derive the application's proof codec dimensions from its trusted circuits.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub fn proof_geometry(
    spec: &ZkSpecStruct,
    signature: &Circuit<P256Field>,
    hash: &Circuit<Gf2_128Field>,
) -> Result<super::MdocProofGeometry, String> {
    use crate::runtime::{
        algebra::{
            fp2::Fp2Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        v2::zk::{joint::JointParam, ZkContext},
    };
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    let ext = Fp2Field::new(&p);
    let hd = BinaryInterpolatorFactory::full_field(&f);
    let sd =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &ext, ext.omega(), ext.omega_order());
    let hc = ZkContext::new(&hd);
    let sc = ZkContext::new(&sd);
    let (h, s) = spec.configs();
    let h = super::adapter::BinaryParticipant::new(hash, h, &hc)?;
    let s = super::adapter::SharedParticipant::new(
        signature,
        crate::mdoc::circuits::p256_adapter::SHARED_BITS,
        s,
        &sc,
    )?;
    let joint = JointParam::new((h.participant(&hc)?, (s.participant(&sc)?, ())))
        .map_err(|e| e.to_string())?;
    Ok(super::MdocProofGeometry {
        geom_hash: h.geometry(),
        geom_sig: s.geometry(),
        joint_context: joint.context(),
        config: joint.config(),
    })
}
