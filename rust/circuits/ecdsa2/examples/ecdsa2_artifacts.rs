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

//! Emit every proof input for the ECDSA2 signature circuit from a single compilation.
//!
//! Usage: `ecdsa2_artifacts OUT_DIR`
//!
//! Writes `ecdsa2.lfc2` (feed to `core-proto`'s `lfc2_to_lean`), `ecdsa2.sidecar`, the
//! `cert::emit_lean` modules under `OUT_DIR/lean`, and `manifest.txt`.
//!
//! One process, one in-memory circuit: the artifact and the certificate advice describe *the
//! same* circuit.  Recompiling separately for each output is not an adequate identity check,
//! because compiler or interface drift can yield superficially similar but different circuits.
//! `manifest.txt` records the geometry and the LFC2 page root so a later `lfc2_to_lean` run can
//! be cross-checked against this one.
//!
//! The layout names are chosen to match the fields of Lean's `EcdsaWitness`, so the final
//! theorem's statement reads in witness vocabulary rather than in wire positions.  Note that
//! the Rust interface is *not* field-for-field identical to the Lean one:
//!
//!   * `ers[i]` is a 3-bit digit packed as `4*e + 2*r + s`, whereas Lean's `bi` packs it as
//!     `e + 2*r + 4*s` -- the same point is selected, but the bit order inside the digit is
//!     reversed (compare `opts` in `circuit.rs` with `muxPoint`'s docstring);
//!   * `round` has 256 entries where Lean's `int_x/int_y/int_z` have `kBits - 1 = 255`;
//!   * `yinv` has no counterpart in Lean's witness.
//!
//! Those are real differences to be discharged by the spec bridge, not naming accidents, so the
//! names below describe the *Rust* wires and the bridge does the translation explicitly.

use std::{fs, path::Path};

use circuits_ecdsa2::EcdsaCircuit;
use compile_algebra::{p256::P256Field, secp256r1::Secp256r1};
use compile_compiler::{cert, compile_with_cert};
use compile_logic::LogicIO;
use core_proto::{commitment::FormalCircuitCommitment, writer::CircuitWriter, FieldID, Layer};

fn main() {
    let out = std::env::args()
        .nth(1)
        .expect("usage: ecdsa2_artifacts OUT_DIR");
    let out = Path::new(&out);
    fs::create_dir_all(out.join("lean")).expect("create OUT_DIR/lean");

    let field = P256Field::new();
    let curve = Secp256r1::new(&field);
    let mut layout = cert::LayoutBuilder::new();

    let (circuit, stats, symbols, schedule_info) = compile_with_cert(&field, |logic| {
        let ecdsa = EcdsaCircuit::new(&logic, &curve);
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;

        // Allocate through the circuit's own allocators, then read each position back off the
        // allocated wire.  Re-deriving the allocation order here would be a second copy of it,
        // free to drift from `allocate.rs` without any check.
        let given = circuits_ecdsa2::allocate_given_wires(&logic, &mut pos);
        let derived = circuits_ecdsa2::allocate_derived_wires(&logic, &mut pos);

        let mut name = |wire: &_, n: String| {
            layout.record(logic.position_in_input_array(wire), n);
        };

        name(&given.pkxy.0, "pkx".into());
        name(&given.pkxy.1, "pky".into());
        name(&given.e, "e".into());
        name(&given.rxy.0, "rx".into());
        name(&given.rxy.1, "ry".into());
        for (i, w) in given.ers.iter().enumerate() {
            name(w, format!("ers{i}"));
        }

        name(&derived.pkxinv, "pkxinv".into());
        name(&derived.rxinv, "rxinv".into());
        name(&derived.nmsinv, "nmsinv".into());
        name(&derived.yinv, "yinv".into());

        // `pre` in Lean is the flat list [GPK.x, GPK.y, GR.x, GR.y, RPK.x, RPK.y, GRPK.x,
        // GRPK.y]; the Rust slicing fields are in the same order, with `pk_r` = RPK.
        let s = &derived.slicing;
        for (j, pt) in [&s.g_pk, &s.g_r, &s.pk_r, &s.g_pk_r].iter().enumerate() {
            name(&pt.0, format!("pre{}", 2 * j));
            name(&pt.1, format!("pre{}", 2 * j + 1));
        }
        for (i, pt) in s.round.iter().enumerate() {
            name(&pt.0, format!("intx{i}"));
            name(&pt.1, format!("inty{i}"));
            name(&pt.2, format!("intz{i}"));
        }

        (ecdsa.assert_signature(&given, &derived), 1, 0)
    });

    // Fails loudly if any input position went unnamed, or was named twice.
    layout.assert_covers(circuit.raw.ninput);

    // `compile_with_cert` leaves every layer as one segment holding all of its deltas
    // (`scheduler.rs`'s `Layer::new_compressed(.., vec![unrolled], vec![0])`).  Finding the
    // repeated runs is a separate pass, and without it the serialized layer -- and the Lean
    // parse module for it -- is proportional to the full expanded term count.
    // `segment_circuit` asserts `compute_id` is unchanged, so this is a re-encoding of the same
    // circuit and the sidecar built from `circuit` still describes it.
    let segmented = compile_compiler::segment_circuit(&field, &circuit);
    assert_eq!(segmented.id, circuit.id, "segmentation changed the circuit id");

    let writer = CircuitWriter::new(&field, FieldID::P256);
    let lfc2 = writer.to_bytes_lfc2(&segmented);
    let lfc2 = writer.to_bytes_lfc2(&segmented);
    let commitment = FormalCircuitCommitment::new(&lfc2);

    // **Build the sidecar from `segmented`, not from `circuit`.** `segment_circuit` sorts the
    // constant table by frequency and renumbers every `k_index` (`segment.rs:198`), so the two
    // circuits carry the *same* constants under *different* numbering. The artifact is written
    // from `segmented`, so `segmented`'s numbering is the one the committed bytes commit to, and
    // a sidecar built from `circuit` would give the DAG's `k_index`es — and `constNat` — a
    // numbering the decoded layer terms do not share.
    //
    // Nothing in `artifactRaw_eq_raw` catches that: the layer terms are *shared* with the
    // artifact rather than compared, and the constant *count* is equal either way. It surfaced
    // only because `backed_check` mentions the index of the zero constant, which was 70 in the
    // sidecar's table and 3 in the artifact's. `corr_check` would also have failed. `constNat`
    // alone would have been silently wrong.
    let sidecar = cert::build_sidecar(
        &field,
        FieldID::P256,
        &segmented,
        &symbols,
        &schedule_info,
        &layout.entries(),
    );
    let parsed = cert::parse_sidecar(&sidecar).expect("sidecar parses");


    // Generation-time guard for the invariant above. Without it the mismatch is invisible until
    // a Lean `decide` comes out false several hundred modules into a build.
    assert_eq!(
        parsed.constants.len(),
        segmented.raw.constants.len(),
        "sidecar and artifact disagree on the constant count"
    );
    for (i, (side, art)) in parsed
        .constants
        .iter()
        .zip(segmented.raw.constants.iter())
        .enumerate()
    {
        assert_eq!(
            side.as_slice(),
            core_algebra::SerializableField::to_bytes(&field, art).as_slice(),
            "constant {i} differs between sidecar and artifact"
        );
    }
    // Cheap guard against the two halves describing different circuits.
    assert_eq!(parsed.id, circuit.id, "sidecar id mismatch");
    assert_eq!(parsed.ninput, stats.ninput, "sidecar ninput mismatch");
    assert_eq!(parsed.layers.len(), stats.nlayers, "sidecar layer mismatch");
    assert_eq!(
        parsed.assertions.len(),
        stats.nassertions,
        "sidecar assertion mismatch"
    );

    fs::write(out.join("ecdsa2.lfc2"), &lfc2).expect("write LFC2");
    fs::write(out.join("ecdsa2.sidecar"), &sidecar).expect("write sidecar");

    for (name, contents) in cert::emit_lean(
        &parsed,
        &cert::EmitOptions {
            name: "Ecdsa2",
            chunk: std::env::var("CHUNK")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(1000),
            // Layer terms normally come from the artifact modules `lfc2_to_lean` writes for the
            // same circuit.  Pass `--no-artifact` to emit a self-contained `raw` instead: the
            // structural checks and everything downstream of `ValidScheduling` do not need the
            // byte chain, so they can be built and measured independently of it.
            artifact: if std::env::args().any(|a| a == "--no-artifact") {
                None
            } else {
                Some("Ecdsa2")
            },
        },
    ) {
        // `cert::emit_lean` now returns paths like `Gen/Sha256Blk/Foo.lean`, so the
        // subdirectory has to exist before the write.
        let path = out.join("lean").join(&name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create Lean module directory");
        }
        fs::write(path, contents).expect("write Lean module");
    }

    let terms: Vec<usize> = circuit.raw.layers.iter().map(Layer::num_terms).collect();
    let manifest = format!(
        "circuit = ecdsa2_signature\n\
         field = p256\n\
         curve = secp256r1\n\
         circuit_id = {}\n\
         lfc2_root = {}\n\
         lfc2_bytes = {}\n\
         lfc2_pages = {}\n\
         lfc2_bytes = {}\n\
         ninput = {}\n\
         npublic_input = {}\n\
         noutput = {}\n\
         nlayers = {}\n\
         nassertions = {}\n\
         nterms = {}\n\
         layer_terms = {terms:?}\n",
        hex(&circuit.id),
        hex(&commitment.root),
        lfc2.len(),
        commitment.page_count,
        lfc2.len(),
        stats.ninput,
        stats.npublic_input,
        stats.noutput,
        stats.nlayers,
        stats.nassertions,
        stats.nterms,
    );
    fs::write(out.join("manifest.txt"), &manifest).expect("write manifest");
    print!("{manifest}");
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
