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

//! Standalone mDoc ZK **verifier** demo (built with only the `verifier` + `mdoc` features).
//!
//! Verifies a proof produced by `prover_only`. Like the prover, it is pinned to the
//! **precompiled Longfellow v1 circuit** [`ZK_SPECS`]`[0]` (ZK-spec version 7, one disclosed
//! attribute) whose `.lfa2` archive is checked into `src/mdoc/artifacts/circuits/`;
//! the NEXT circuits (`mdoc::proto::NEXT_VERSION`, version 12) are only synthesised by
//! `compiler` builds and are not exercised here.
//!
//! ```text
//! verifier_only [--circuit <path>] [<proof-in-path>]
//!
//!   --circuit <path>   Circuit archive (.lfa2) to verify against. Overrides the
//!                      LONGFELLOW_MDOC_CIRCUIT environment variable; when neither is given,
//!                      the checked-in artifact (resolved relative to the crate root at build
//!                      time) is used. Must match the archive used by the prover.
//!   <proof-in-path>    Proof to verify. Defaults to ./mdoc_zk_proof.bin.
//! ```

use std::path::{Path, PathBuf};

use longfellow_zk::mdoc::v1::{req_attr, run_mdoc_verifier, ZK_SPECS};

/// Environment variable that overrides the default circuit-archive location.
const CIRCUIT_ENV_VAR: &str = "LONGFELLOW_MDOC_CIRCUIT";
/// Default proof input, relative to the current working directory.
const DEFAULT_PROOF_FILE: &str = "mdoc_zk_proof.bin";
/// Upper bound on the proof file we are willing to load; real proofs are well below 1 MiB.
const MAX_PROOF_BYTES: u64 = 32 * 1024 * 1024;

const PKX: &str = "0xb4682ec20e06e8df840b5dd32959798ab20c544d4da50109ff4684d06fd261fc";
const PKY: &str = "0xf6f8e9a811911329a5f653fcec5990092c91a65bc1695d291cd51de9c94e7db7";
const NOW: &str = "2025-04-30T00:00:00Z";
const DOC_TYPE: &str = "org.iso.18013.5.1.mDL";

const TRANSCRIPT: &[u8] = &[
    0x83, 0xf6, 0xf6, 0x84, 0x71, 0x42, 0x72, 0x6f, 0x77, 0x73, 0x65, 0x72, 0x48, 0x61, 0x6e, 0x64,
    0x6f, 0x76, 0x65, 0x72, 0x76, 0x31, 0x58, 0x20, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
    0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
    0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x58, 0x35, 0xa3, 0x63, 0x63, 0x61, 0x74, 0x01,
    0x64, 0x74, 0x79, 0x70, 0x65, 0x01, 0x67, 0x64, 0x65, 0x74, 0x61, 0x69, 0x6c, 0x73, 0xa1, 0x67,
    0x62, 0x61, 0x73, 0x65, 0x55, 0x72, 0x6c, 0x77, 0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x72,
    0x65, 0x6c, 0x79, 0x69, 0x6e, 0x67, 0x70, 0x61, 0x72, 0x74, 0x79, 0x2e, 0x63, 0x6f, 0x6d, 0x58,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40,
];

/// Command-line options for the demo.
struct Options {
    circuit_override: Option<PathBuf>,
    proof_path: PathBuf,
}

fn usage() -> String {
    format!(
        "usage: verifier_only [--circuit <path>] [<proof-in-path>]\n\
         \n\
         Verifies the proof in <proof-in-path> (default: ./{DEFAULT_PROOF_FILE}) against the\n\
         Longfellow v1 / circuit v7 circuit ZK_SPECS[0] and the embedded test transcript/issuer key.\n\
         The circuit archive is taken from --circuit, else ${CIRCUIT_ENV_VAR}, else the\n\
         checked-in artifact under src/mdoc/artifacts/circuits/."
    )
}

fn parse_args(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let mut circuit_override = None;
    let mut proof_path = None;
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        if arg == "-h" || arg == "--help" {
            println!("{}", usage());
            std::process::exit(0);
        } else if arg == "--circuit" {
            let value = iter.next().ok_or("--circuit requires a path argument")?;
            circuit_override = Some(PathBuf::from(value));
        } else if let Some(value) = arg.strip_prefix("--circuit=") {
            circuit_override = Some(PathBuf::from(value));
        } else if arg.starts_with('-') {
            return Err(format!("unknown option `{arg}`\n{}", usage()));
        } else if proof_path.is_none() {
            proof_path = Some(PathBuf::from(arg));
        } else {
            return Err(format!("unexpected extra argument `{arg}`\n{}", usage()));
        }
    }
    Ok(Options {
        circuit_override,
        proof_path: proof_path.unwrap_or_else(|| PathBuf::from(DEFAULT_PROOF_FILE)),
    })
}

/// Resolves the circuit archive: `--circuit` > `LONGFELLOW_MDOC_CIRCUIT` > checked-in artifact.
fn resolve_circuit_path(override_path: Option<PathBuf>, hash_hex: &str) -> PathBuf {
    override_path
        .or_else(|| std::env::var_os(CIRCUIT_ENV_VAR).map(PathBuf::from))
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("src/mdoc/artifacts/circuits")
                .join(format!("{hash_hex}.lfa2"))
        })
}

/// Loads the (untrusted) proof file, never buffering more than `MAX_PROOF_BYTES`.
fn read_proof(path: &Path) -> Result<Vec<u8>, String> {
    use std::io::Read;

    let file = std::fs::File::open(path).map_err(|e| {
        format!(
            "failed to read proof from {} (run `prover_only` first): {e}",
            path.display()
        )
    })?;
    let mut proof = Vec::new();
    file.take(MAX_PROOF_BYTES + 1)
        .read_to_end(&mut proof)
        .map_err(|e| format!("failed to read proof from {}: {e}", path.display()))?;
    if proof.len() as u64 > MAX_PROOF_BYTES {
        return Err(format!(
            "proof file {} exceeds the {MAX_PROOF_BYTES}-byte limit",
            path.display()
        ));
    }
    Ok(proof)
}

fn run() -> Result<(), String> {
    let opts = parse_args(std::env::args().skip(1))?;

    // Longfellow v1 / circuit v7 / 1-attribute circuit: the only version with a checked-in
    // artifact.
    let spec = &ZK_SPECS[0];
    let circuit_path = resolve_circuit_path(opts.circuit_override, &spec.combined_hash_hex());
    let circuits = std::fs::read(&circuit_path).map_err(|e| {
        format!(
            "failed to read circuit archive {}: {e}",
            circuit_path.display()
        )
    })?;
    let attrs = [req_attr("org.iso.18013.5.1", "age_over_18", [0xf5])];
    let proof = read_proof(&opts.proof_path)?;

    run_mdoc_verifier(
        spec, &circuits, PKX, PKY, TRANSCRIPT, &attrs, NOW, DOC_TYPE, &proof,
    )
    .map_err(|e| format!("mdoc verifier rejected the proof: {e:?}"))?;
    println!(
        "Verified mdoc ZK proof ({} bytes, zk-spec v{}, circuit {}) from {}",
        proof.len(),
        spec.version,
        circuit_path.display(),
        opts.proof_path.display()
    );
    Ok(())
}

fn main() {
    if let Err(msg) = run() {
        eprintln!("verifier_only: {msg}");
        std::process::exit(1);
    }
}
