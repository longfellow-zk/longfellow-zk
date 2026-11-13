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

use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::{
            archive::{CircuitArchive, CircuitArchiveBuilder},
            v2::{
                Circuit, CircuitReader, CircuitWriter, Layer, Quadratic, RawCircuitBuilder, Stream,
            },
            FieldID,
        },
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

fn tiny<F: SerializableField + AlgebraicField>(f: &F) -> Circuit<F> {
    let raw = RawCircuitBuilder {
        ninput: 1,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.one()],
        layers: vec![Layer::with_assertions(
            1,
            Stream::<Quadratic>::from_terms([Quadratic {
                g: 0,
                l: 0,
                r: 0,
                k: 0,
            }]),
            Stream::default(),
            Stream::default(),
            |_| false,
        )],
    }
    .build();
    Circuit::from_raw(f, raw)
}
fn fixture(p: &P256Field, f: &Gf2_128Field) -> CircuitArchive {
    let sig = tiny(p);
    let hash = tiny(f);
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(crate::mdoc::circuits::NEXT_VERSION as u32);
    builder.add_entry(
        "sig",
        sig.id,
        CircuitWriter::new(p, FieldID::P256).to_bytes(&sig),
    );
    builder.add_entry(
        "hash",
        hash.id,
        CircuitWriter::new(f, FieldID::Gf2_128).to_bytes(&hash),
    );
    builder.build()
}
fn compressed(archive: &CircuitArchive) -> Vec<u8> {
    zstd::encode_all(archive.to_bytes_lfa2().as_slice(), 1).unwrap()
}

#[test]
fn circuit_identifier_enforcement_is_unconditional() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let mut archive = fixture(&p, &f);
    decompress_circuits(&compressed(&archive), &p, &f).unwrap();
    let original = archive.combined_id;
    let (circuit, _) = CircuitReader::new(&p, FieldID::P256)
        .from_bytes(&archive.entries[0].payload)
        .unwrap();
    let stale_id = circuit.id;
    let mut raw = circuit.into_raw().into_builder();
    raw.constants[0] = p.zero();
    let raw = raw.build();
    let circuit = Circuit::from_raw(&p, raw);
    let mut payload = CircuitWriter::new(&p, FieldID::P256).to_bytes(&circuit);
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
        version: crate::mdoc::circuits::NEXT_VERSION,
        polygero_hash: super::super::zk_spec::PolygeroParameters {
            k: 349,
            n: 2443,
            s: 12,
            t: 84,
        },
        polygero_sig: super::super::zk_spec::PolygeroParameters {
            k: 349,
            n: 2443,
            s: 12,
            t: 84,
        },
    };
    assert!(for_spec(&spec, &compressed(&archive), &p, &f).is_err());
}

/// the spec pins the archive and each payload matches its entry.
#[test]
fn for_spec_binds_archive_and_entry_identifiers() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let spec_for = |combined_hash| super::ZkSpecStruct {
        combined_hash,
        num_attributes: 1,
        version: crate::mdoc::circuits::NEXT_VERSION,
        polygero_hash: super::super::zk_spec::PolygeroParameters {
            k: 349,
            n: 2443,
            s: 12,
            t: 84,
        },
        polygero_sig: super::super::zk_spec::PolygeroParameters {
            k: 349,
            n: 2443,
            s: 12,
            t: 84,
        },
    };
    let archive = fixture(&p, &f);
    assert!(for_spec(
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
        for_spec(&spec_for(other), &compressed(&archive), &p, &f).is_err(),
        "archive accepted under a different spec combined hash"
    );
    // Valid payloads whose directory entry names a different circuit ID.
    let sig = tiny(&p);
    let hash = tiny(&f);
    let mut wrong = sig.id;
    wrong[0] ^= 1;
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(crate::mdoc::circuits::NEXT_VERSION as u32);
    builder.add_entry(
        "sig",
        wrong,
        CircuitWriter::new(&p, FieldID::P256).to_bytes(&sig),
    );
    builder.add_entry(
        "hash",
        hash.id,
        CircuitWriter::new(&f, FieldID::Gf2_128).to_bytes(&hash),
    );
    let mismatched = builder.build();
    assert!(
        for_spec(
            &spec_for(mismatched.combined_id),
            &compressed(&mismatched),
            &p,
            &f
        )
        .is_err(),
        "payload accepted under a different archive entry ID"
    );
}
