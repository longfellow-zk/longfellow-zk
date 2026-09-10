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

//! Reproduce the small Rung1 artifact used by the Lean end-to-end ingestion test.
//!
//! Emits both halves, because `Gen/Rung1` needs both and neither is checked in:
//!
//! * the LFC2 payload, which `lfc2_to_lean` turns into the pages, commitment and staged decode;
//! * the `cert::emit_lean` modules (`Rung1Nodes*`, `Rung1OkCheck`, `Rung1InvCheck`,
//!   `Rung1ArtifactCommitment`, ...), which are steps 2-3 and come from the *source* compile --
//!   the LFC2 bytes carry no layout names or assertion scope paths, so they cannot be recovered
//!   from the artifact.
//!
//! ```text
//! cargo run --release -p circuits-ec --example rung1_lfc2 -- OUT.lfc2 [LEAN_OUT_DIR]
//! cargo run --release -p core-proto --example lfc2_to_lean -- \
//!     p256 OUT.lfc2 ../formal/circuits/quadcert Rung1
//! ```

use circuits_ec::EcCircuit;
use compile_algebra::{p256::P256Field, secp256r1::Secp256r1};
use compile_compiler::{cert, cert::LayoutBuilder, compile_with_cert};
use compile_logic::Logic;
use core_proto::{writer::CircuitWriter, FieldID, Layer};

fn main() {
    let output = std::env::args()
        .nth(1)
        .expect("usage: rung1_lfc2 OUTPUT.lfc2 [LEAN_OUT_DIR]");
    let lean_out = std::env::args().nth(2);
    let field = P256Field::new();
    let curve = Secp256r1::new(&field);
    let mut layout = LayoutBuilder::new();
    let (circuit, stats, symbols, schedule_info) = compile_with_cert(&field, |logic| {
        let ec = EcCircuit::new(&logic, &curve);
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let px = layout.next(&logic, &mut position, "px");
        let py = layout.next(&logic, &mut position, "py");
        let qx = layout.next(&logic, &mut position, "qx");
        let qy = layout.next(&logic, &mut position, "qy");
        let qz = layout.next(&logic, &mut position, "qz");
        let zinv = layout.next(&logic, &mut position, "zinv");
        let equality = ec.point_equality(&(qx, qy, qz), &zinv, &(px, py));
        let on_curve = ec.is_on_curve(&(px, py));
        (logic.assert_all("rung1", &[equality, on_curve]), 1, 0)
    });
    layout.assert_covers(circuit.raw.ninput);
    eprintln!(
        "ninput={} constants={} terms={:?}",
        circuit.raw.ninput,
        circuit.raw.constants.len(),
        circuit
            .raw
            .layers
            .iter()
            .map(Layer::num_terms)
            .collect::<Vec<_>>()
    );
    let bytes = CircuitWriter::new(&field, FieldID::P256).to_bytes_lfc2(&circuit);
    std::fs::write(output, bytes).expect("write Rung1 LFC2");

    // Steps 2-3.  `build_sidecar` asserts `compute_id == circuit.id`, so this is pinned to the
    // same circuit the LFC2 payload above was written from -- there is no segmentation pass
    // here to renumber constants between them.
    let Some(lean_out) = lean_out else { return };
    let sidecar = cert::build_sidecar(
        &field,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        &layout.entries(),
    );
    let parsed = cert::parse_sidecar(&sidecar).expect("sidecar parses");
    assert_eq!(parsed.id, circuit.id, "sidecar id mismatch");
    assert_eq!(parsed.ninput, stats.ninput, "sidecar ninput mismatch");
    assert_eq!(parsed.layers.len(), stats.nlayers, "sidecar layer mismatch");
    for (name, contents) in cert::emit_lean(
        &parsed,
        &cert::EmitOptions { name: "Rung1", chunk: 2000, artifact: Some("Rung1Artifact") },
    ) {
        let path = std::path::Path::new(&lean_out).join(&name);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create Lean module directory");
        }
        std::fs::write(path, contents).expect("write Lean module");
    }
    eprintln!("emitted cert modules under {lean_out}/Gen/Rung1");
}
