// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Extract the two shipped mdoc circuits as standalone LFC2 blobs, which is what
//! `core-proto`'s `lfc3_to_lean` example ingests.
//!
//! The checked-in archive bundles both circuits, so nothing downstream can read one on its own;
//! this splits them.  **The circuits are segmented first**, because `segment_circuit` sorts the
//! constant table by frequency and renumbers every `k_index`: the artifact has to be written from
//! the same circuit any sidecar is built from, or the DAG's constant indices name a different
//! table than the decoded layer terms do.
//!
//! ```text
//! cargo run --release -p mdoc-zk-runtime --bin mdoc_lfc2 -- OUT_DIR [CIRCUIT_HASH]
//! cargo run -p core-proto --example lfc3_to_lean -- \
//!     gf2_128 OUT_DIR/mdoc_hash.lfc2 ../formal/circuits/quadcert MdocHash
//! ```

use compile_compiler::segment_circuit;
use core_proto::{writer::CircuitWriter, FieldID, Layer, SerializableField};
use mdoc_zk_runtime::proto::decompress_circuits;

/// The artifact `mdoc_layer_probe` measures, so the two agree by default.
const DEFAULT_MDOC_HASH: &str = "8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121";

fn emit<F: SerializableField + Clone>(
    field: &F,
    field_id: FieldID,
    label: &str,
    circuit: &core_proto::circuit::Circuit<F>,
    out_dir: &str,
) {
    let segmented = segment_circuit(field, circuit);
    assert_eq!(
        segmented.id, circuit.id,
        "segmentation changed the {label} circuit id"
    );
    let writer = CircuitWriter::new(field, field_id);
    let lfc2 = writer.to_bytes_lfc2(&segmented);
    let path = format!("{out_dir}/mdoc_{label}.lfc2");
    std::fs::write(&path, &lfc2).unwrap_or_else(|e| panic!("write {path}: {e}"));
    println!(
        "{label}: {} layers, {} terms, {} constants, ninput={} -> {} ({} bytes)",
        segmented.raw.layers.len(),
        segmented.raw.layers.iter().map(Layer::num_terms).sum::<usize>(),
        segmented.raw.constants.len(),
        segmented.raw.ninput,
        path,
        lfc2.len()
    );
}

fn main() {
    let mut args = std::env::args().skip(1);
    let out_dir = args.next().unwrap_or_else(|| {
        eprintln!("usage: mdoc_lfc2 OUT_DIR [CIRCUIT_HASH]");
        std::process::exit(2)
    });
    let hash = args.next().unwrap_or_else(|| DEFAULT_MDOC_HASH.to_string());
    std::fs::create_dir_all(&out_dir).expect("create OUT_DIR");

    let compressed = mdoc_zk_artifacts::load_circuit_lfa2(&hash);
    let p256 = runtime_algebra::p256::P256Field::new();
    let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();
    let (sig, hash_circuit) =
        decompress_circuits(&compressed, &p256, &gf2).expect("decode checked-in mdoc artifact");

    println!("mdoc artifact {hash}: transport={} bytes", compressed.len());
    emit(&p256, FieldID::P256, "sig", &sig, &out_dir);
    emit(&gf2, FieldID::Gf2_128, "hash", &hash_circuit, &out_dir);
}
