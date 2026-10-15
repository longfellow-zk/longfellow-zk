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

//! Emit every proof input for the one-block SHA-256 circuit from a single compilation.
//!
//! Usage: `sha256_artifacts OUT_DIR`
//!
//! Writes `sha256.lfc2` (feed to `core-proto`'s `lfc2_to_lean`), `sha256.sidecar`, the
//! `cert::emit_lean` modules under `OUT_DIR/lean`, and `manifest.txt`.
//!
//! The point of doing all of this in one process is that the artifact and the certificate
//! advice describe *the same in-memory circuit*.  Recompiling the source separately for each
//! output is not an adequate identity check: compiler or interface drift can yield
//! superficially similar but different circuits.  `manifest.txt` records the geometry and the
//! LFC2 page root so a later `lfc2_to_lean` run can be cross-checked against this one.

use std::{fs, path::Path};

use circuits_bitvec::{BitvecIO, BitvecLogic};
use circuits_sha256::Sha256;
use circuits_analog_adder::FieldWrappingSum;
use compile_algebra::{field::CompileField, gf2_128::Gf2_128Field, p256::P256Field};
use compile_compiler::{cert, compile_with_cert};
use core_proto::{commitment::FormalCircuitCommitment, writer::CircuitWriter, FieldID, Layer};

/// SHA-256 words are 32 bits wide, and each bit is its own input wire.
const WORD_BITS: usize = 32;

fn main() {
    let out = std::env::args()
        .nth(1)
        .expect("usage: sha256_artifacts OUT_DIR [--field=p256|gf2_128]");
    let out = Path::new(&out);
    fs::create_dir_all(out.join("lean")).expect("create OUT_DIR/lean");

    // Which field the one-block circuit is compiled over.  `p256` is the historical default and
    // the one the proved `Sha256Blk` bridge is about; `gf2_128` is the field the *deployed* mdoc
    // hash circuit uses, where `assert_wrapping_sum` is the multiplicative embedding rather than
    // the positional one (`analog_adder/src/circuit.rs:117` vs `:58`).
    let which = std::env::args()
        .find_map(|a| a.strip_prefix("--field=").map(str::to_string))
        .unwrap_or_else(|| "p256".to_string());

    match which.as_str() {
        "p256" => emit(&P256Field::new(), FieldID::P256, "p256", "Sha256Blk", out),
        "gf2_128" => emit(
            &Gf2_128Field::new(),
            FieldID::Gf2_128,
            "gf2_128",
            "Sha256Gf2",
            out,
        ),
        other => panic!("unsupported field {other:?}; expected p256 or gf2_128"),
    }
}

/// Compile, segment, commit, and emit the one-block SHA-256 artifact over `field`.
///
/// `lean_name` is the generated namespace and directory (`Gen/{lean_name}/`), so the two fields'
/// module sets never collide.
fn emit<F>(field: &F, field_id: FieldID, field_name: &str, lean_name: &'static str, out: &Path)
where
    F: CompileField + core_algebra::SerializableField + FieldWrappingSum + Clone,
{
    let mut layout = cert::LayoutBuilder::new();

    let (circuit, stats, symbols, schedule_info) = compile_with_cert(field, |logic| {
        let sha256 = Sha256::new(&logic);
        let bv = BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bv);
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;

        // Allocate through the circuit's own allocators, then read each word's base position
        // back off the allocated value.  Re-deriving the allocation order here instead would
        // be a second copy of it, free to drift from `allocate.rs` without any check.
        let given = circuits_sha256::allocate_given(&bv, &mut pos);
        let derived = circuits_sha256::allocate_derived(&bv, &mut pos);

        let name_word = |words: &[_], group: &str, layout: &mut cert::LayoutBuilder| {
            for (index, word) in words.iter().enumerate() {
                layout.record_range(
                    io.position_in_input_array(word),
                    WORD_BITS,
                    &format!("{group}{index}"),
                );
            }
        };
        name_word(&given.input_block, "input_block", &mut layout);
        name_word(&given.h0, "h0_", &mut layout);
        name_word(&derived.outw, "outw", &mut layout);
        name_word(&derived.oute, "oute", &mut layout);
        name_word(&derived.outa, "outa", &mut layout);
        name_word(&derived.h1, "h1_", &mut layout);

        (
            sha256.assert_transform_block(&given, &derived),
            1,
            0,
        )
    });

    // Fails loudly if any input position went unnamed, or was named twice.
    layout.assert_covers(circuit.raw.ninput);

    // `compile_with_cert` leaves every layer as one segment holding all of its deltas
    // (`scheduler.rs`'s `Layer::new_compressed(.., vec![unrolled], vec![0])`).  Finding the
    // repeated runs is a separate pass, and without it the serialized layer — and the Lean
    // parse module for it — is proportional to the full expanded term count.
    // `segment_circuit` asserts `compute_id` is unchanged, so this is a re-encoding of the
    // same circuit and the sidecar built from `circuit` still describes it.
    let segmented = compile_compiler::segment_circuit(field, &circuit);
    assert_eq!(segmented.id, circuit.id, "segmentation changed the circuit id");


    // The hand-written bridges are written against one particular circuit: they name node ids,
    // and node numbering comes out of the compiler. Determinism makes regeneration reproducible
    // but not drift-proof -- `S2TmplBool`'s worked instance broke when input 1 moved from node
    // 14939 to 14925 between the bridge being written and a later compile, and it surfaced as an
    // unprovable Lean side goal hundreds of modules downstream rather than here.
    //
    // `EXPECT_CIRCUIT_ID=<hex>` turns that into a generation-time failure. The value the bridges
    // were written against is recorded in `formal/circuits/quadcert/CIRCUIT_PINS.txt`.
    if let Ok(want) = std::env::var("EXPECT_CIRCUIT_ID") {
        let got = hex(&circuit.id);
        assert_eq!(
            got,
            want.trim(),
            "circuit drift: this compile is {got}, but the bridges were written against {}. \
             Either regenerate the hand-written node tables or update the pin.",
            want.trim()
        );
    }
    let writer = CircuitWriter::new(field, field_id);
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
        field,
        field_id,
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
            core_algebra::SerializableField::to_bytes(field, art).as_slice(),
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

    fs::write(out.join("sha256.lfc2"), &lfc2).expect("write LFC2");
    fs::write(out.join("sha256.sidecar"), &sidecar).expect("write sidecar");

    for (name, contents) in cert::emit_lean(
        &parsed,
        &cert::EmitOptions {
            name: lean_name,
            // Chunk size is a memory knob: SHA-256's node records are bigger than ECDSA2's,
            // and 2000 exceeds a 9 GB cap on `Nodes0`.  Override with CHUNK=<n>.
            chunk: std::env::var("CHUNK")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(2000),
            // Layer terms normally come from the artifact modules `lfc2_to_lean` writes for
            // the same circuit.  Pass `--no-artifact` to emit a self-contained `raw` instead:
            // the structural checks and everything downstream of `ValidScheduling` do not need
            // the byte chain, so they can be built and measured independently of it.
            artifact: if std::env::args().any(|a| a == "--no-artifact") {
                None
            } else {
                Some(lean_name)
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
        "circuit = sha256_block\n\
         field = {field_name}\n\
         circuit_id = {}\n\
         lfc2_root = {}\n\
         lfc2_bytes = {}\n\
         lfc2_pages = {}\n\
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
