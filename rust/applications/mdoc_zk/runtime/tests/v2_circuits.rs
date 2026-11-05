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

//! Longfellow v2 circuit-loader flag tests.

use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::{
            archive::{CircuitArchive, CircuitArchiveBuilder},
            v2::{
                compute_id, Circuit, CircuitReader, CircuitWriter, Layer, Quadratic, RawCircuit,
                Stream,
            },
            FieldID,
        },
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

fn tiny<F: SerializableField + AlgebraicField>(f: &F) -> Circuit<F> {
    let raw = RawCircuit {
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
    };
    Circuit {
        id: compute_id(f, &raw),
        raw,
    }
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
fn circuit_identifier_enforcement_is_opt_in() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let mut archive = fixture(&p, &f);
    decompress_circuits(&compressed(&archive), &p, &f, true).unwrap();
    let original = archive.combined_id;
    let (mut circuit, _) = CircuitReader::new(&p, FieldID::P256)
        .from_bytes(&archive.entries[0].payload, true)
        .unwrap();
    circuit.raw.constants[0] = p.zero();
    let stale_id = circuit.id;
    circuit.id = compute_id(&p, &circuit.raw);
    let mut payload = CircuitWriter::new(&p, FieldID::P256).to_bytes(&circuit);
    let id_offset = payload.len() - stale_id.len();
    payload[id_offset..].copy_from_slice(&stale_id);
    archive.entries[0].payload = payload;
    assert_eq!(archive.combined_id, original);
    assert!(
        decompress_circuits(&compressed(&archive), &p, &f, true).is_err(),
        "explicit ID enforcement must reject a payload with a stale identifier"
    );
    // Trusted loads preserve the C++ flag contract and pay no ID-recomputation cost.
    decompress_circuits(&compressed(&archive), &p, &f, false).unwrap();
}
