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

//! V2 loader flag tests use LFC3 payloads in LFA2.
use super::*;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField, SupportsU64Conversions},
        proto::{
            archive::{CircuitArchive, CircuitArchiveBuilder},
            fixed::CoefficientClasses,
            reader::CircuitReader,
            v2::{compute_id, Circuit, Layer, Quadratic, RawCircuit, Stream},
            writer::CircuitWriter,
            FieldID,
        },
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
fn tiny<F: SerializableField + AlgebraicField>(f: &F) -> Circuit<F> {
    let mut bytes = vec![0; f.serialized_size_bytes()];
    bytes[0] = 2;
    let raw = RawCircuit {
        ninput: 1,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.bytes_to_element(&bytes).unwrap()],
        layers: vec![Layer {
            nw: 1,
            logw: 0,
            quadratic: Stream::<Quadratic>::from_terms([Quadratic {
                g: 0,
                l: 0,
                r: 0,
                k: 0,
            }]),
            ..Default::default()
        }],
    };
    let coefficient_classes = CoefficientClasses::ALL.for_field(f.is_binary());
    Circuit {
        id: compute_id(f, &raw, coefficient_classes),
        raw,
        coefficient_classes,
    }
}
fn fixture(p: &P256Field, f: &Gf2_128Field) -> CircuitArchive {
    let sig = tiny(p);
    let hash = tiny(f);
    let mut b = CircuitArchiveBuilder::new();
    b.set_circuit_version(9);
    b.add_entry(
        "sig",
        sig.id,
        CircuitWriter::new(p, FieldID::P256).to_bytes_lfc3(&sig),
    );
    b.add_entry(
        "hash",
        hash.id,
        CircuitWriter::new(f, FieldID::Gf2_128).to_bytes_lfc3(&hash),
    );
    let manifest = crate::mdoc::proto::packed::HashInputManifest {
        public_bits: 1,
        private_bits: 0,
    };
    b.add_entry("hash-input", manifest.digest(), manifest.to_bytes());
    b.build()
}
fn compressed(a: &CircuitArchive) -> Vec<u8> {
    zstd::encode_all(a.to_bytes_lfa2().as_slice(), 1).unwrap()
}
#[test]
fn circuit_identifier_enforcement_is_opt_in() {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let mut archive = fixture(&p, &f);
    decompress_circuits(&compressed(&archive), &p, &f, true).unwrap();
    let original = archive.combined_id;
    let (mut c, _) = CircuitReader::new(&p, FieldID::P256)
        .from_bytes_lfc3(&archive.entries[0].payload, true)
        .unwrap();
    let stale_id = c.id;
    c.raw.constants[0] = p.u64_to_element(3);
    c.id = compute_id(&p, &c.raw, c.coefficient_classes);
    let mut payload = CircuitWriter::new(&p, FieldID::P256).to_bytes_lfc3(&c);
    let n = payload.len();
    payload[n - 32..].copy_from_slice(&stale_id);
    archive.entries[0].payload = payload;
    assert_eq!(archive.combined_id, original);
    assert!(
        decompress_circuits(&compressed(&archive), &p, &f, true).is_err(),
        "ID enforcement must reject a stale semantic ID"
    );
    decompress_circuits(&compressed(&archive), &p, &f, false).unwrap();
}
