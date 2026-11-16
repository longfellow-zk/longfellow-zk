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

//! Longfellow v2 circuit-loader identity checks.

use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::{
            archive::{CircuitArchive, CircuitArchiveBuilder},
            v2::{
                Circuit, CircuitReader, CircuitWriter, Layer, Quadratic, RawCircuitBuilder, Stream,
            },
        },
    },
    mdoc::{
        proto::NEXT_VERSION,
        v2::{circuits::*, inputs::PublicInputs, req_attr, request::Request},
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

/// The signature and hash public-input counts of DESIGN.md I3 for the
/// one-attribute requests of these tests: 258 and 901 + 788.
const PUBLIC_INPUTS: [usize; 2] = [258, 1689];

/// A one-layer circuit whose inputs are all `npublic` public inputs.
fn tiny<F: SerializableField + AlgebraicField>(f: &F, npublic: usize) -> Circuit<F> {
    let raw = RawCircuitBuilder {
        ninput: npublic,
        npublic_input: npublic,
        noutput: 1,
        logv: 0,
        constants: vec![f.one()],
        layers: vec![Layer::new(
            npublic,
            Stream::<Quadratic>::from_terms([Quadratic {
                g: 0,
                l: 0,
                r: 0,
                k: 0,
            }]),
            Stream::default(),
            Stream::default(),
        )],
    }
    .build();
    Circuit::from_raw(f, raw)
}
fn fixture(p: &P256Field, f: &Gf2_128Field) -> CircuitArchive {
    fixture_with(p, f, PUBLIC_INPUTS)
}
/// An archive whose circuits have `[signature, hash]` public inputs.
fn fixture_with(p: &P256Field, f: &Gf2_128Field, public: [usize; 2]) -> CircuitArchive {
    let sig = tiny(p, public[0]);
    let hash = tiny(f, public[1]);
    let mut builder = CircuitArchiveBuilder::new();
    builder.circuit_version = Some(NEXT_VERSION as u32);
    builder.add_entry("sig", sig.id, CircuitWriter::new(p).to_bytes(&sig));
    builder.add_entry("hash", hash.id, CircuitWriter::new(f).to_bytes(&hash));
    builder.build()
}
fn compressed(archive: &CircuitArchive) -> Vec<u8> {
    zstd::encode_all(archive.to_bytes_lfa2().as_slice(), 1).unwrap()
}

/// Load an archive for a valid one-attribute request under `spec`.
fn load_for(
    spec: &super::ZkSpecStruct,
    compressed: &[u8],
    p: &P256Field,
    f: &Gf2_128Field,
) -> Result<Instance, String> {
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let request = Request::check(
        spec,
        "1",
        "2",
        b"\x66inputs",
        &attrs,
        "2026-10-23T00:00:00Z",
        "doc",
        p,
    )
    .expect("the test request passes the request check");
    Instance::load(&request, compressed, p, f)
}

#[test]
fn circuit_identifier_enforcement_is_unconditional() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let mut archive = fixture(&p, &f);
    decompress_circuits(&compressed(&archive), &p, &f).unwrap();
    let original = archive.combined_id;
    let (circuit, _) = CircuitReader::new(&p)
        .from_bytes(&archive.entries[0].payload)
        .unwrap();
    let stale_id = circuit.id;
    let mut raw = circuit.into_raw().into_builder();
    raw.constants[0] = p.zero();
    let raw = raw.build();
    let circuit = Circuit::from_raw(&p, raw);
    let mut payload = CircuitWriter::new(&p).to_bytes(&circuit);
    let id_offset = payload.len() - stale_id.len();
    payload[id_offset..].copy_from_slice(&stale_id);
    archive.entries[0].payload = payload;
    assert_eq!(archive.combined_id, original);
    assert!(
        decompress_circuits(&compressed(&archive), &p, &f).is_err(),
        "loading must reject a payload with a stale identifier"
    );
    let spec = super::ZkSpecStruct {
        combined_hash: archive.combined_id,
        num_attributes: 1,
        version: NEXT_VERSION,
        polygero: super::super::MDOC_JOINT_PROFILE,
    };
    assert!(load_for(&spec, &compressed(&archive), &p, &f).is_err());
}

/// the spec pins the archive and each payload matches its entry.
#[test]
fn instance_load_binds_archive_and_entry_identifiers() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let spec_for = |combined_hash| super::ZkSpecStruct {
        combined_hash,
        num_attributes: 1,
        version: NEXT_VERSION,
        polygero: super::super::MDOC_JOINT_PROFILE,
    };
    let archive = fixture(&p, &f);
    assert!(load_for(
        &spec_for(archive.combined_id),
        &compressed(&archive),
        &p,
        &f
    )
    .is_ok());
    // A self-consistent archive that the spec does not name.
    let mut other = archive.combined_id;
    other[0] ^= 1;
    assert!(
        load_for(&spec_for(other), &compressed(&archive), &p, &f).is_err(),
        "archive accepted under a different spec combined hash"
    );
    // Valid payloads whose directory entry names a different circuit ID.
    let sig = tiny(&p, PUBLIC_INPUTS[0]);
    let hash = tiny(&f, PUBLIC_INPUTS[1]);
    let mut wrong = sig.id;
    wrong[0] ^= 1;
    let mut builder = CircuitArchiveBuilder::new();
    builder.circuit_version = Some(NEXT_VERSION as u32);
    builder.add_entry("sig", wrong, CircuitWriter::new(&p).to_bytes(&sig));
    builder.add_entry("hash", hash.id, CircuitWriter::new(&f).to_bytes(&hash));
    let mismatched = builder.build();
    assert!(
        load_for(
            &spec_for(mismatched.combined_id),
            &compressed(&mismatched),
            &p,
            &f
        )
        .is_err(),
        "payload accepted under a different archive entry ID"
    );
}

/// The loader requires DESIGN.md I3's public-input counts, `901 + 788 * A`
/// for the hash circuit and 258 for the signature circuit, and those are the
/// lengths both roles derive from the request.
#[test]
fn instance_load_checks_public_input_counts() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let spec_for = |combined_hash| super::ZkSpecStruct {
        combined_hash,
        num_attributes: 1,
        version: NEXT_VERSION,
        polygero: super::super::MDOC_JOINT_PROFILE,
    };
    let attrs = [req_attr("namespace", "a", [0xf5])];
    let spec = spec_for([0; 32]);
    let request = Request::check(
        &spec,
        "1",
        "2",
        b"\x66inputs",
        &attrs,
        "2026-10-23T00:00:00Z",
        "doc",
        &p,
    )
    .unwrap();
    let public = PublicInputs::derive(&request, &p);
    assert_eq!(
        [public.signature().len(), public.hash().len()],
        PUBLIC_INPUTS
    );
    assert_eq!(super::hash_public_inputs(1), Some(PUBLIC_INPUTS[1]));
    assert_eq!(super::hash_public_inputs(4), Some(4053));
    assert_eq!(super::hash_public_inputs(usize::MAX), None);

    // The honest instance loads.
    let honest = fixture(&p, &f);
    assert!(load_for(&spec_for(honest.combined_id), &compressed(&honest), &p, &f).is_ok());
    // Each self-consistent archive the spec names, but with a wrong count, is
    // rejected; 2477 is the hash count for two attributes.
    for counts in [
        [258, 1688],
        [258, 1690],
        [258, 2477],
        [257, 1689],
        [259, 1689],
        [1689, 258],
    ] {
        let archive = fixture_with(&p, &f, counts);
        assert!(
            load_for(
                &spec_for(archive.combined_id),
                &compressed(&archive),
                &p,
                &f
            )
            .is_err(),
            "loaded circuits with {counts:?} public inputs"
        );
    }
}
